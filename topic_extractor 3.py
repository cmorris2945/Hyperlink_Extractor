# -*- coding: utf-8 -*-
"""
Created on Tue Nov 19 10:46:18 2019
@author: Chris Morris
"""
from . import paths
import os
import sys
import re
import logging
from bs4 import BeautifulSoup
import clr
import spacy.lang.en
import datetime
from word2number import w2n
import dateutil.parser

sys.path.append(paths.py_contract_bot_root_dir)
import pdfprocessor

logger = logging.getLogger(__name__)

class Document:
    """
    the main class that holds all info relevant to an document being processed
    """

    ### prioritized Topics for summary
    # sections_to_summarize_by_priority = ['GENERAL:','REFILL REQUIREMENTS:', 'WORK STATEMENT:', 'OBJECTIVE:', 'TASKS:', 'DELIVERABLES:', 'SOFTWARE AND TECHNOLOGY:', 'SYSTEMS:', 'REQUIREMENTS:', 'CONTRACT LINE ITEMS:']
    sections_to_summarize_by_priority = ['GENERAL:', 'DOCUMENT REQUIREMENTS:', 'REFILL REQUIREMENTS:', 'INDICATIONS:']
    
    ### used for cleaning text before summarizing
    replace_regexes = [(re.compile('\S{22,}', flags=re.IGNORECASE|re.DOTALL)) # overLongWordsAndHashes
                      ]

    #################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################
    ## Period of Performance regexes, match groups, and keys
    period_pattern = r'((option(al)?\s*(period|year)?\s*((\d{1,3})|(one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve)|(\b[\w ]{1,30}\b))?)|(based?\s*(period)?(\b[\w: ]{0,30}\b))|(award-?\s*(term)?\s*((\d{1,3})|(one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve))?))\s*\)?'
    filler_pattern = r'\s*([-:‐–]|of)*\s*'
    length_of_time_words_pattern = r'\(?\s*(((\d+)|((one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|twenty[‐–-]one|twenty[‐–-]two|twenty[‐–-]three|twenty[‐–-]four)\s*(\(\d+\))?))\s*\)?\s*[‐–-]*\s*((days?)|(months?)|(years?)))'
    length_of_time_dates_pattern = r'\(?\s*(((((\d{2}|\d{1})[\/\\])((\d{2}|\d{1})[\/\\])*(\d{4}|\d{2}))|(((Jan(uary)?|Feb(ruary)?|Mar(ch)?|May|Apr(il)?|Jul(y)|Jun(e)?|Aug(ust)?|Oct(ober)|Sep(tember)?|Nov(ember)?|Dec(ember)?)\s*\.?\s*\d+(st|nd|rd|th)*,?\s*(\d{4}|\d{2}))))\s*([-:‐–]|through|to|thru| )\s*((((\d{2}|\d{1})[\/\\])((\d{2}|\d{1})[\/\\])*(\d{4}|\d{2}))|(((Jan(uary)?|Feb(ruary)?|Mar(ch)?|May|Apr(il)?|Jul(y)|Jun(e)?|Aug(ust)?|Oct(ober)|Sep(tember)?|Nov(ember)?|Dec(ember)?)\s*\.?\s*\d+(st|nd|rd|th)*,?\s*(\d{4}|\d{2})))))'
    
    full_pattern_words = period_pattern + filler_pattern + length_of_time_words_pattern
    full_pattern_dates = period_pattern + filler_pattern + length_of_time_dates_pattern

    full_period_words_re = re.compile(full_pattern_words, re.IGNORECASE)
    full_period_dates_re = re.compile(full_pattern_dates, re.IGNORECASE)

    option_period_match_group = 2
    option_period_number_match_group = 5
    base_period_match_group = 9

    award_term_period_match_group = 12
    award_term_period_number_match_group = 14

    duration_match_group = 18
    duration_number_match_group = 20
    duration_number_second_match_group = 22

    days_match_group = 25
    months_match_group = 26
    years_match_group = 27

    date_duration_match_group = 18
    date1_match_group = 19
    date2_match_group = 43

    base_key = 'base'
    duration_words_key = 'dur_words'
    dates_key = 'dates'
    catch_all_key = 'catch_all'
    mult_words_key = 'mult_words'
    #################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################################

    def __init__(self, doc_id, name, parsed_html_file_path):
        """
        initialize all member vars
        """
        self.doc_id = doc_id
        self.name = name
        self.parsed_html_file_path = parsed_html_file_path
        self.topics = []
        self.topics_dict = {}
        self.subtopics = []
        self.reg_matches = []
        self.cluster_matches = []
        self.sections = []

        self.all_lines=[]
        self.all_text=''

        self.text_to_summarize = ''
        self.text_to_summarize_list = []
        self.text_to_summarize_name_list = []
        self.text_to_summarize_dict = {}
        self.topics_added_to_summary = {}

        self.summary = ''
        self.period_of_performance = ''
        self.period_of_performance_lines_added = []
        self.period_of_performance_lines_added_indices = []
        self.period_of_performance_dict = {}
        self.period_of_performance_total_days = ''

        self.contract_data = {}

        self.text_to_summarize_raw = ''

        self.debug_html_file = None

    def add_topic(self, topic):
        """
        adds Topic to Document
        """
        self.topics.append(topic)
        self.topics_dict[topic.name] = topic

    def get_topics_by_subtopic_id(self, subtopic_id):
        """
        returns Topics associated with a Subtopic ID
        """

        topics_to_return = []
        for topic in self.topics:
            if subtopic_id in topic.subtopic_ids:
                topics_to_return.append(topic)
        return topics_to_return
    
    def get_topic_by_name(self, topics, name):
        """
        returns a Topic by name
        """

        for topic in self.topics:
            if name == topic.name:
                return topic

    def get_regmatch_by_regmatch_id(self, regmatch_id):
        """
        returns a RegMatch by RegMatch ID
        """

        for reg_match in self.reg_matches:
            if regmatch_id == reg_match.subtopic_id:
                return reg_match 
        return None  

    def get_subtopic_by_subtopic_id(self, subtopic_id):
        """
        returns a RegMatch by RegMatch ID
        """

        for subtopic in self.subtopics:
            if subtopic_id == subtopic.subtopic_id:
                return subtopic 
        return None  

    def add_text_to_summarize(self, topic):
        """
        cleans text then adds text for summary
        """

        text_to_add = self.clean_text_for_summary(topic=topic)
        text_added = False

        if text_to_add.strip() != '':
            self.text_to_summarize += '\n' 
            self.text_to_summarize += text_to_add
            
            self.text_to_summarize_raw += '\n' 
            self.text_to_summarize_raw += topic.text

            self.text_to_summarize_list.append(text_to_add)
            self.text_to_summarize_dict[topic.name] = topic
            self.text_to_summarize_name_list.append(topic.name)
            text_added = True
            
        return text_added

    def clean_text_for_summary(self, topic):
        """
        cleans text for summary
        removes any repeated text
        """

        text = topic.text
        for section_ind, section in enumerate(topic.sections):
            if section.text in self.text_to_summarize_raw:
                text = text.replace(section.text, '')
                logger.debug('REMOVE REPEATED SECTION TEXT in SECTION ' + str (section_ind) + ' OF TOPIC ' + str(topic.name) + ' FROM TEXT TO SUMMARIZE:: ' + str(section.text))
        for custom_line in topic.custom_line_elements_added:
            if custom_line.text in self.text_to_summarize_raw:
                text = text.replace(custom_line.text, '')
                logger.debug('REMOVE REPEATED CUSTOM LINE TEXT OF TOPIC ' + str(topic.name) + ' FROM TEXT TO SUMMARIZE:: ' + str (custom_line.text))

        for replace_regex in self.replace_regexes:
            text = replace_regex.sub('', text)

        return text

class Topic:
    """
    class to represent a Topic
    Topics are set up in Reportables file before processing
    Sections are assigned Topics
    holds SubTopics (RegMatches and ClusterMatches), text, line elements, and Sections
    """

    def __init__(self, name):
       self.name = name
       self.subtopics = []
       self.subtopic_ids = []
       self.regmatches = []
       self.regmatch_ids = []
       self.clustermatches = []
       self.clustermatch_ids = []
       self.sections = []
       self.sections_added_by = []
       self.sections_scores = {}
       self.text = ''
       self.line_elements = []
       ## this can be used for line-level regexes when the entire section isn't added
       self.custom_line_elements = []
       self.custom_line_elements_added = []

       self.custom_line_element_indices = []
       self.line_element_indices = []

       
    def add_subtopic(self, new_subtopic):
        """
        adds a SubTopic to the Topic
        """

        self.subtopics.append(new_subtopic)
        self.subtopic_ids.append(new_subtopic.subtopic_id)
        if new_subtopic.is_regex:
            self.regmatches.append(new_subtopic)
            self.regmatch_ids.append(new_subtopic.subtopic_id)
        else:
            self.clustermatches.append(new_subtopic)
            self.clustermatch_ids.append(new_subtopic.subtopic_id)
            
    def add_section(self, new_section, custom_lines=None, custom_line_indices=None, added_by=''):
        """
        adds a Section to the Topic
        """

        if not custom_lines:
            if new_section not in self.sections:
                self.sections.append(new_section)
                self.sections_added_by.append(added_by)
        else:
            self.custom_line_elements.extend(custom_lines)
            self.custom_line_element_indices.extend(custom_line_indices)
        
    def update_text_and_line_elements(self):
        """
        sometimes text is added to Sections one line at a time, but Sections are added to Topic right when the Section is create (only the first line of text in the Section at this time)
        have to wait until after processing entire Document before adding all of the Section text to the Topic
        fucntion to update the text in the Topic after processing the Document has finshed
        dont add repeated lines
        """

        for section in self.sections:
            if self.text != '':
                self.text += ' '
            self.text += section.text
            # self.text += '.'
            self.line_elements.extend(section.line_elements)
            self.line_element_indices.extend(section.line_element_indices)

        last_line_index_added = None
        for loop_index, custom_line_element in enumerate(self.custom_line_elements):
            if custom_line_element not in self.line_elements:
                
                if self.text != '':
                    # if last_line_index_added and (last_line_index_added != self.custom_line_element_indices[loop_index] - 1):
                    #     self.text += '.'
                    #     logger.debug('adding period bc custom line does NOT follow previous line in doc: ' + str(last_line_index_added) + ' --> ' + str(self.custom_line_element_indices[loop_index]))
                    # else:
                    #     logger.debug('not adding period bc custom line follows previous line in doc: ' + str(last_line_index_added) + ' --> ' + str(self.custom_line_element_indices[loop_index]))
                    self.text += ' '

                self.line_elements.append(custom_line_element)
                self.line_element_indices.append(self.custom_line_element_indices[loop_index])
                last_line_index_added = self.custom_line_element_indices[loop_index]
                # TODO: add period to text for sentencizer --- commented out -- didnt like it
                logger.debug('adding custom line: ' + str(custom_line_element.get_text().encode("utf-8")))
                self.text += custom_line_element.get_text() 
                self.custom_line_elements_added.append(custom_line_element)
            else:
                logger.debug('skipping duplicate line: ' + str(custom_line_element.get_text().encode("utf-8")))
        
        # if self.text.strip() != '':
        #     self.text += '.'
            
class SubTopic:
    """
    parent class for RegMatch and ClusterMatch
    """

    def __init__(self, name, is_regex, subtopic_id):
       self.name = name
       self.is_regex = is_regex
       self.subtopic_id = subtopic_id
       self.sections=[]
       
class RegMatch(SubTopic):
    """
    inherits from SubTopic
    represents a regular expression match found from ContractBot
    """

    reg_match_ele_re = re.compile('id_.*')  
    # title_words = ['scope', 
    #                'scope of work',
    #                'period of performance', 
    #                'performance period',
    #                'background', 
    #                'tasks', 
    #                'introduction', 
    #                'overview', 
    #                'summary', 
    #                'objective', 
    #                'objectives', 
    #                'requirements', 
    #                'requirements definition',
    #                'deliverables',
    #                'deliverable',
    #                'clins',
    #                'contract line items',
    #                'work statement',
    #                'work statements',
    #                'purpose']

    specific_titles = {'GENERAL:': [r'general information'],
                       'DOCUMENT REQUIREMENTS:': [r'(?!general *\w+)general']
                    }
                   
                   

    title_words = [
                   'refill requirements',
                   'indications'
                  ]
                  
    STATIC_TITLES_TO_ADD = ['Period of Performance', 'Scope of Work']
    title_regex_matches = []
    @classmethod
    def build_title_match_strings(cls):
        """
        class method to build the title match list of strings from title_words class var
        adds variations of captitalized letters and ':'
        """

        if not cls.title_regex_matches:
            cls.title_regex_matches.extend(cls.STATIC_TITLES_TO_ADD)
            for title in cls.title_words:
                capitalized_title = title.capitalize()
                
                cls.title_regex_matches.append(title.upper())
                cls.title_regex_matches.append(title.title())
                # check to see if title() version is same as capitalized() version
                if capitalized_title not in cls.title_regex_matches:
                    cls.title_regex_matches.append(capitalized_title)
                    cls.title_regex_matches.append(capitalized_title+':')

                cls.title_regex_matches.append(title.upper()+':')
                cls.title_regex_matches.append(title.title()+':')

                #test lowercase with :
                # cls.title_regex_matches.append(title+':')
                
        logger.debug('TITLE STRINGS: ' + str(cls.title_regex_matches))

    def __init__(self, name, is_regex, subtopic_id):
       super().__init__(name=name, is_regex=True, subtopic_id=subtopic_id)
       
     
class ClusterMatch(SubTopic):
    """
    inherits from SubTopic
    represents a machine learning topic match found from ContractBot
    """

    def __init__(self, name, is_regex, subtopic_id):
       super().__init__(name=name, is_regex=False, subtopic_id=subtopic_id)
       self.clusters=[]
       self.cluster_index_of_name=None
       
    def add_cluster(self, new_cluster):
       """
       adds a cluster to the ClusterMatch
       """

       self.clusters.append(new_cluster)

class Cluster:
    """
    a ClusterMatch can hold multiple clusters with different scores
    """

    def __init__(self, name, score):
       self.name=name
       self.score=score
       
class Section:
    """
    represents a small part of text from the input doc - usually a paragraph - seperated by whitespace
    """

    def __init__(self, section_head=None, section_head_text=''):
       self.section_head_lines = []
       self.section_head_lines.append(section_head)
       self.section_head_text = section_head_text
       self.text = ''
       self.line_elements = []
       self.topics = []

       self.line_element_indices = []

    def add_text(self, new_text):
        """
        adds text to the section
        """
        self.text += ' '
        self.text += new_text
        
    def add_section_head_line(self, new_section_head_line):
        """
        a section header line is a line of text in the doc that starts a new section
        """

        self.section_head_lines.append(new_section_head_line)
        
    def add_section_head_text(self, new_text):
        """
        adds the text of the section header line
        """

        self.section_head_text += ' '
        self.section_head_text += new_text
        
    def add_line_element(self, new_element, line_index):
        """
        adds a line element to the section
        """
        self.line_elements.append(new_element)
        self.line_element_indices.append(line_index)
        
    def add_topic(self, new_topic):
        """
        adds a topic to the section
        """
        self.topics.append(new_topic)
    
def assign_topic_and_section(document, section, subtopic_id, custom_lines=None, custom_line_indices=None, added_by=''):
    """
    adds topics and sections based on subtopic ids
    """

    topics_matched = document.get_topics_by_subtopic_id(subtopic_id)
    
    for topic in topics_matched:
        topic.add_section(section, custom_lines=custom_lines, custom_line_indices=custom_line_indices, added_by=added_by)
        if not custom_lines:
            section.add_topic(topic)
        
def find_regex_matches(line_ele, line_ele_index, section, document, title_match=False, line_match=False, add_surrounding_lines=False,line_prior=None, line_after=None, current_cluster_id=None):
    """
    main function to assign topics and sections based on regmatches
    """

    add_next_section = False
    subtopic_id_to_add_next = None
    line_reg_matches= line_ele.find_all('span', {"id" : RegMatch.reg_match_ele_re})
    custom_lines=[]
    custom_line_indices = []
    if add_surrounding_lines:
        if line_prior:
            custom_lines.append(line_prior)
            custom_line_indices.append(line_ele_index-1)
        custom_lines.append(line_ele)
        custom_line_indices.append(line_ele_index)
        if line_after:
            custom_lines.append(line_after)
            custom_line_indices.append(line_ele_index+1)
    else:
        custom_lines.append(line_ele)
        custom_line_indices.append(line_ele_index)

    for reg_match in line_reg_matches:
        custom_lines_copy = custom_lines.copy()
        custom_line_indices_copy = custom_line_indices.copy()
        subtopic_regmatch_id = reg_match['id']

        subtopic_match = document.get_regmatch_by_regmatch_id(regmatch_id=subtopic_regmatch_id)

        topics_matched = document.get_topics_by_subtopic_id(subtopic_regmatch_id)
        topics_matched_names = []
        for topic_matched in topics_matched:
            topics_matched_names.append(topic_matched.name)
        ## we want all lines with period of performance reg matches
        if 'PERIOD OF PERFORMANCE:' in topics_matched_names:
            assign_topic_and_section(document, section, subtopic_regmatch_id, custom_lines=custom_lines_copy, custom_line_indices=custom_line_indices_copy, added_by='REGEX MATCH: ' + str(custom_lines_copy))

        ## for non-section head lines
        ## primarily used to check for section headers that were added to the end of a section instead of starting a new one
        if title_match:
            # subtopic_match = document.get_regmatch_by_regmatch_id(regmatch_id=subtopic_regmatch_id)
            if subtopic_match:
                if subtopic_match.name in RegMatch.title_regex_matches:

                    ## check for line_after being new section -- add next section
                    is_section_head_next, _subtopic_cluster_id, _current_cluster_id = check_for_section_head(rr_line=line_after, subtopic_cluster_id=None, current_cluster_id=current_cluster_id)
                    if is_section_head_next:
                        add_next_section = True
                        custom_lines_copy.pop()
                        custom_line_indices_copy.pop()
                        subtopic_id_to_add_next = subtopic_match.subtopic_id
                    else:
                        ## test add entire section
                        # assign_topic_and_section(document, section, subtopic_regmatch_id, custom_lines=None, custom_line_indices=None, added_by='non section header regex title match - add entire section ')
                        # assign_topic_and_section(document, section, subtopic_regmatch_id, custom_lines=custom_lines_copy, custom_line_indices=custom_line_indices_copy, added_by='non section header regex title match - CLs = ' + str(custom_lines_copy))
                        pass
        elif line_match:
            assign_topic_and_section(document, section, subtopic_regmatch_id, custom_lines=custom_lines_copy, custom_line_indices=custom_line_indices_copy, added_by='CUSTOM LINE')
            
        ## assuming only matching for section header-  add entire section
        else: 
            ## only title matches
            # subtopic_match = document.get_regmatch_by_regmatch_id(regmatch_id=subtopic_regmatch_id)
            if subtopic_match:
                if subtopic_match.name in RegMatch.title_regex_matches:
                    assign_topic_and_section(document, section, subtopic_regmatch_id, custom_lines=None, custom_line_indices=None, added_by = 'SECTION HEADER')
     
    return add_next_section, subtopic_id_to_add_next

def parse_topics(rr_section_boxes, document, add_all_clusters=False, cluster_cutoff_score=0.0):
    """
    parses the html file to create Topics
    """

    logger.debug('begin parsing topics out of section boxes')
    logger.debug("add_all_clusters = " +str(add_all_clusters) + "; if true will check if highest cluster score is cluster match name and or cluster match name cluster score is greater than threshold")
    for rr_section_box in rr_section_boxes:
        topic_name = rr_section_box['key']

        ## topic name
        # logger.error(topic_name)
        ####

        ## create Topic
        new_topic = Topic(name=topic_name)
        ## loop through ML ClusterMatches and add them to Topic
        cluster_elements = rr_section_box.find_all('span','sectionStats')
        for cluster_element in cluster_elements:
            ######
            # logger.error(cluster_element.findNext('span').get_text())
            #########

            new_cluster_match = ClusterMatch(name=cluster_element.findNext('span').get_text(), is_regex=False, subtopic_id=cluster_element['id_off'])
            
            ## parse ML cluster for cluster names and scores- try to add them
            ## ex: Option Agreement: 86%, Type of Option: 82%, Option Period: 82%
            clusters_text = cluster_element.get_text()
            clusters_text_split = clusters_text.split('%')
            for cluster_index, cluster_text in enumerate(clusters_text_split):
                if ':' in cluster_text:
                    cluster_text_score_split = cluster_text.split(':')
                    cluster_name = ''
                    for split_ind, split_text in enumerate(cluster_text_score_split[:-1]):
                        # if not first text element, add back in the : for the name
                        if split_ind > 0:
                            cluster_name += ':'
                            logger.debug('FOUND : IN CLUSTER NAME: ' + str(split_text))
                        cluster_name += split_text
                    cluster_name = cluster_name.strip(', ')
                    cluster_score = float(cluster_text_score_split[len(cluster_text_score_split)-1])
                    new_cluster = Cluster(name=cluster_name, score=cluster_score)
                    new_cluster_match.add_cluster(new_cluster)
                    if cluster_name == new_cluster_match.name:
                        new_cluster_match.cluster_index_of_name = cluster_index

            if new_cluster_match.cluster_index_of_name == None:
                logger.error("no cluster index for name..........")
                logger.error("cluster name: " + str(new_cluster_match.name))
                for ind, cluster in enumerate(new_cluster_match.clusters):
                    logger.error('cluster ' + str(ind+1) + 'name: '+ str(cluster.name))
                logger.error("setting cluster_index_of_name to 0 for fail safe")
                new_cluster_match.cluster_index_of_name = 0
        
            ## determine if clustermatch should be added an used in doc
            add_cluster_match = True
            # need to check highest rating to weed out topics
            if not add_all_clusters:
                logger.debug('add_all_clusters = False; checking if clustermatch name == highest scoring cluster')
                ## check name in topic to see if it matches highest scoring cluster
                if new_cluster_match.cluster_index_of_name != 0:
                    logger.debug('ClusterMatch name is not highest score; id = ' + str(cluster_element['id_off'])+ ', name = ' + str(new_cluster_match.name) + ', best_score = ' +  str(new_cluster_match.clusters[0].name))
                    logger.debug('comparing score of named cluster to score threshold')
                    ## try score threshold   
                    if new_cluster_match.clusters[new_cluster_match.cluster_index_of_name].score < cluster_cutoff_score:
                        logger.debug('cluster name score < score threshold; do not add cluster match: ' + str(new_cluster_match.clusters[new_cluster_match.cluster_index_of_name].score) + ' < ' + str(cluster_cutoff_score) )
                        add_cluster_match = False
                    else:
                        logger.debug('clustermatch name score >= score threshold; add the clustermatch: ' + str(new_cluster_match.clusters[new_cluster_match.cluster_index_of_name].score) + ' >= ' + str(cluster_cutoff_score) )

                else:
                    logger.debug('clustermatch highest scored cluster matches name; add the clustermatch: ' + str(cluster_element['id_off'])+ ', name = ' + str(new_cluster_match.name) + ', best_score = ' +  str(new_cluster_match.clusters[0].name))
            else:
                logger.debug('add_all_clusters = True; adding cluster')

            if add_cluster_match:
                document.subtopics.append(new_cluster_match)
                document.cluster_matches.append(new_cluster_match)
                new_topic.add_subtopic(new_cluster_match)
                         
        ## loop through RegMatches and add them to Topic
        reg_match_elements = rr_section_box.find_all('span', {"id_off" : RegMatch.reg_match_ele_re})
        for reg_match_element in reg_match_elements:
            new_reg_match = RegMatch(name=reg_match_element.get_text(), is_regex=True, subtopic_id=reg_match_element['id_off'])
            document.subtopics.append(new_reg_match)
            document.reg_matches.append(new_reg_match)
            new_topic.add_subtopic(new_reg_match)
              
        document.add_topic(topic=new_topic)

def check_for_section_head(rr_line, subtopic_cluster_id, current_cluster_id):
    """
    returns if line is a section header or not
    """

    is_section_head = False
    ## check for section head    
    if rr_line.find('div', 'section'):
        subtopic_cluster_id = rr_line.find('div','section')['id']
        ## check for page break sections
        if '_top' in subtopic_cluster_id:
            # skip_until_next_topic = True
            subtopic_cluster_id = subtopic_cluster_id.strip("_top")
            
        # this is just in case the section started with a page broken "_top" section
        if subtopic_cluster_id != current_cluster_id:
            is_section_head = True
            current_cluster_id = subtopic_cluster_id

    return is_section_head, subtopic_cluster_id, current_cluster_id

def parse_sections(rr_lines, document):
    """
    parses the Sections in the html doc
    """

    RegMatch.build_title_match_strings()
    section_heads = []
    still_need_section_header = False         
    current_section = None
    current_cluster_id = None
    add_next_section = False
    subtopic_cluster_id = None
    added_to_section_header_text = False
    previous_line_was_section_header = False
    previous_top = None
    first_line_after_full_section_head = False

    ## loop through all the lines in the doc
    for line_index, rr_line in enumerate(rr_lines):
        
        line_text = rr_line.get_text()

        if '•' in line_text:
            line_text = line_text.replace('•', '.')

        ## skip lines
        if re.search('Created on', line_text):
            continue

        is_section_head, subtopic_cluster_id, current_cluster_id = check_for_section_head(rr_line=rr_line, subtopic_cluster_id=subtopic_cluster_id, current_cluster_id=current_cluster_id)

        ## if section head, create new section
        if is_section_head:
            section_heads.append(rr_line)
            current_section = Section(section_head=rr_line, section_head_text=line_text)
            assign_topic_and_section(document, current_section, subtopic_cluster_id, custom_lines=None, custom_line_indices=None, added_by='ML CLUSTER MATCH')
            ## add_next_section is True when a RegMatch title ended the last section
            if add_next_section:
                logger.debug('ADDING NEXT SECTION BC TITLE MATCH ENDED PREV SECTION: ' + str(subtopic_id_to_add_next))
                assign_topic_and_section(document, current_section, subtopic_id_to_add_next, custom_lines=None, custom_line_indices=None, added_by='SECTION HEADER 2')
            document.sections.append(current_section)
            ## check section head text for matching regex
            find_regex_matches(line_ele=rr_line,
                               line_ele_index=line_index,
                               section=current_section,
                               document=document,
                               title_match=False,
                               line_match=False)
            ## if section header line is only number title (e.g. '3.'), add next line too
            if re.search('[a-zA-Z]{2,}', line_text):
                still_need_section_header = False
                # logger.error(f'SECTION HEAD TEXT: {subtopic_cluster_id}:: {current_section.section_head_text}')
            else:
                still_need_section_header = True

            added_to_section_header_text = True
              
        ## is not technically section head - 
        ## check for adding addition text to section head text (for when section head text == "1.")
        else:
            if current_section:
                if still_need_section_header:
                    current_section.add_section_head_line(rr_line)
                    current_section.add_section_head_text(line_text)
                    ## check section head text for matching regex
                    find_regex_matches(line_ele=rr_line,
                                       line_ele_index=line_index,
                                       section=current_section,
                                       document=document,
                                       title_match=False,
                                       line_match=False)
                    if re.search('[a-zA-Z]{2,}', line_text):
                        still_need_section_header = False
                        # logger.error(f'SECTION HEAD TEXT: {subtopic_cluster_id}:: {current_section.section_head_text}')
                    else:
                        still_need_section_header = True

                    added_to_section_header_text = True

                else:
                    added_to_section_header_text = False

        if not added_to_section_header_text:  
            if previous_line_was_section_header:
                current_top = rr_line.get('style').split('top:')[1].split('px')[0]
                if previous_top:
                    if previous_top == current_top:
                        current_section.add_section_head_line(rr_line)
                        current_section.add_section_head_text(line_text)

                        added_to_section_header_text = True

                        # logger.error(f'SECTION HEAD TEXT: {subtopic_cluster_id}:: {current_section.section_head_text}')

            
        if first_line_after_full_section_head:
            logger.error("FIRST LINE AFTER FULL SECTION HEAD")
            for topic_key in RegMatch.specific_titles.keys():
                for reg_to_search in RegMatch.specific_titles[topic_key]:
                    if re.search(reg_to_search, current_section.section_head_text, flags=re.IGNORECASE):
                        logger.debug(f"found specific title match: {reg_to_search} :: {current_section.section_head_text}")

                        document.topics_dict[topic_key].add_subtopic(document.get_subtopic_by_subtopic_id(subtopic_cluster_id))
                        assign_topic_and_section(document, current_section, subtopic_cluster_id, custom_lines=None, custom_line_indices=None, added_by = 'SECTION HEADER 3')


        ## check for regex TITLE matches
        custom_lines = []
        try:
            line_prior = rr_lines[line_index-1]
        except(IndexError):
            line_prior = None
        try:
            line_after = rr_lines[line_index+1]
        except(IndexError):
            line_after = None
            
        custom_lines = []
        ## match regex titles
        add_next_section, subtopic_id_to_add_next = find_regex_matches( line_ele=rr_line,
                                                                        line_ele_index=line_index,
                                                                        section=current_section,
                                                                        document=document,
                                                                        title_match=True,
                                                                        line_match=False,
                                                                        add_surrounding_lines=True,
                                                                        line_prior = None,
                                                                        line_after = line_after,
                                                                        current_cluster_id=current_cluster_id)
        
        if current_section:
            current_section.add_text(line_text)
            current_section.add_line_element(rr_line, line_index)
        
        document.all_text += ' '
        document.all_text += line_text
        document.all_lines.append(rr_line)

        previous_top = rr_line.get('style').split('top:')[1].split('px')[0]
        # logger.error(previous_top)

        if not added_to_section_header_text and previous_line_was_section_header:
            first_line_after_full_section_head = True
        else:
            first_line_after_full_section_head = False

        previous_line_was_section_header = added_to_section_header_text

        if 'anti-inflammatory medications or analgesics' in line_text:
            logger.error(line_text)
        
    
def parse_html(doc_id, input_base_name, input_file_path, add_all_clusters=False, cluster_cutoff_score=0.0):
     """
     parse the html file for Topics and Sections
     """

     with open(input_file_path, encoding="utf-8") as html_file:
        html_contents = html_file.read()
        soup = BeautifulSoup(html_contents, 'html.parser')
        
        new_document = Document(doc_id=doc_id, name=input_base_name, parsed_html_file_path=input_file_path)

        ### parse the topics
        rr_section_boxes = soup.find_all('div', 'rr_section_box')
        parse_topics(rr_section_boxes=rr_section_boxes, document=new_document, add_all_clusters=add_all_clusters, cluster_cutoff_score=cluster_cutoff_score)
            
        ### parse rr_lines --> the actual doc text
        rr_lines = soup.find_all('div', 'rr_line')
         
        ### parse the sections; assign topics
        parse_sections(rr_lines=rr_lines, document=new_document)
            
        for topic in new_document.topics:
            topic.update_text_and_line_elements()
            logger.debug(topic.name)
            # logger.debug(topic.text)
            
        return new_document

def scrape_pop_days_duration_words(periods, text):
    """
    format 1 for finding period of performance in text
    e.g. option period 4: 12 months
    """

    periods[Document.duration_words_key] = {}

    ## loop through all matches of format
    for match_ind, match in enumerate(re.finditer(Document.full_period_words_re, text)):
        found_period = False

        period_key = ''

        ## check for base period or option or award periods

        ## if base period
        if match.group(Document.base_period_match_group):
            logger.debug('found base period')
            period_key = Document.base_key
            found_period = True
            
        ## if option period
        elif match.group(Document.option_period_match_group):
            option_title = match.group(Document.option_period_match_group)
       
            logger.debug(str(option_title))
            
            ## find option period number to keep track of the options and not repeat them
            option_number = None
            
            ## check for option period number match group from regex
            if match.group(Document.option_period_number_match_group):
                option_number = match.group(Document.option_period_number_match_group)
                try:
                    option_number = w2n.word_to_num(option_number)
                except Exception as e:
                    logger.error('could not convert option number using w2n: ' + str(match.group(Document.option_period_number_match_group)))
                    option_number = None

            if option_number:
                period_key = 'option_'+ str(option_number)
            ## if generic option period, count it as option period 1
            else:
                if option_title.lower().strip() == 'option period':
                    option_number = 1
                    period_key = 'option_'+ str(option_number)
                ## else, assign period key to the option title found
                else:
                    period_key = str(option_title)
                
            found_period = True

        ## check for award period(s)
        elif match.group(Document.award_term_period_match_group):
            award_title = match.group(Document.award_term_period_match_group)
            logger.debug(str(award_title))
            
            ## find award period number to keep track of the awards and not repeat them
            award_number = None
            
            ## check for award period number match group from regex
            if match.group(Document.award_term_period_number_match_group):
                award_number = match.group(Document.award_term_period_number_match_group)

                try:
                    award_number = w2n.word_to_num(award_number)
                except Exception as e:
                    logger.error('could not convert award number using w2n: ' + str(match.group(Document.award_term_period_number_match_group)))
                    award_number = None

            if award_number:
                period_key = 'award_'+ str(award_number)
            else:
                ## if generic award period, count it as option period 1
                if award_title.lower().strip() == 'award term' or award_title.lower().strip() == 'award-term' or award_title.lower().strip() == 'award–term':
                    award_number = 1
                    period_key = 'award_'+ str(award_number)
                ## else, assign period to to text that was found
                else:
                    period_key = str(award_title)
                
            found_period = True


        ## if valid period found, parse it
        if found_period:
            logger.debug('found pop period!')  
            logger.debug(str(period_key))

            ## check to see if it's a repeated period key; if not, attempt to parse
            if period_key not in periods[Document.duration_words_key].keys():
                logger.debug('unique period found; attempting to add')

                ## check for duration words match group
                ## e.g. 12 months
                if match.group(Document.duration_match_group):
                    if match.group(Document.duration_number_match_group):
                        try:
                            duration_number = int(match.group(Document.duration_number_match_group))
                        except Exception as e:
                            logger.error('duration number cannot be converted to int for: ' + str(period_key))
                            logger.error( str(e))
                            logger.error(type(e).__name__)
                            continue
                    
                    ## different matchgroup for number words 
                    ## e.g. two
                    elif match.group(Document.duration_number_second_match_group):
                        try:
                            duration_number = w2n.word_to_num(match.group(Document.duration_number_second_match_group))
                        except Exception as e:
                            logger.error('duration number (word) cannot be converted to int for: ' + str(period_key))
                            logger.error( str(e))
                            logger.error(type(e).__name__)
                            continue

                    periods[Document.duration_words_key][period_key] = {'text': match.group(Document.duration_match_group)}
                    periods[Document.duration_words_key][period_key]['number'] =  duration_number

                    ## try to convert the duration to a datetime.timedelta object
                    try:
                        if match.group(Document.days_match_group):
                            periods[Document.duration_words_key][period_key]['unit'] = 'days'
                            periods[Document.duration_words_key][period_key]['duration'] = datetime.timedelta(days=duration_number)
                        elif match.group(Document.months_match_group):
                            periods[Document.duration_words_key][period_key]['unit'] = 'months'
                            periods[Document.duration_words_key][period_key]['duration'] = datetime.timedelta(days=round(duration_number*30.41))
                        elif match.group(Document.years_match_group):
                            periods[Document.duration_words_key][period_key]['unit'] = 'years'
                            periods[Document.duration_words_key][period_key]['duration'] = datetime.timedelta(days=duration_number*365)
                    except Exception as e:
                            logger.error('could not create timedelta for : ' + str(period_key))
                            del periods[Document.duration_words_key][period_key]
                            logger.error( str(e))
                            logger.error(type(e).__name__)
                            continue
                        
                    try:
                        periods[Document.duration_words_key][period_key]['days'] = periods[Document.duration_words_key][period_key]['duration'].days
                    except Exception as e:
                        logger.error('could not read WORD duration correctly for: ' + str(period_key))
                        del periods[Document.duration_words_key][period_key]
                        logger.error(str(e))
                        logger.error(type(e).__name__)
                        continue
            
                else:
                    logger.warning('could not add period... duration match group not found')

            else:
                logger.warning('not overwriting duplicate period of performance period: ' + str(period_key))


    return periods

def scrape_pop_days_dates(periods, text):
    """
    format 2 for finding period of performance in text
    e.g. option period 1: July, 2020 - July, 2023
    """

    periods[Document.dates_key] = {}

    ## loop through format regex matches
    for match_ind, match in enumerate(re.finditer(Document.full_period_dates_re, text)):
        found_period = False

        period_key = ''

        ## check for base period vs option period vs award period

        # base period
        if match.group(Document.base_period_match_group):
            logger.debug('found base period')
            period_key = Document.base_key
            found_period = True
            
        # option period
        elif match.group(Document.option_period_match_group):
            option_title = match.group(Document.option_period_match_group)
            logger.debug(str(option_title))
            
            ## find option period number - used to not repeat option periods
            option_number = None

            ## check option number match group
            if match.group(Document.option_period_number_match_group):
                option_number = match.group(Document.option_period_number_match_group)
                try:
                    option_number = w2n.word_to_num(option_number)
                except Exception as e:
                    logger.error('could not convert option number using w2n: ' + str(match.group(Document.option_period_number_match_group)))
                    option_number = None

            if option_number:
                period_key = 'option_'+ str(option_number)
            ## if option number not found
            else:
                ## if generic option period found, assign it as option period 1
                if option_title.lower().strip() == 'option period':
                    option_number = 1
                    period_key = 'option_'+ str(option_number)
                ## else, assign the period key to text that was found
                else:
                    period_key = str(option_title)
                
            found_period = True

        ## award period
        elif match.group(Document.award_term_period_match_group):
            award_title = match.group(Document.award_term_period_match_group)
            logger.debug(str(award_title))
            
            ## find award period number - used to not repeat award periods
            award_number = None
            
            if match.group(Document.award_term_period_number_match_group):
                award_number = match.group(Document.award_term_period_number_match_group)
                try:
                    award_number = w2n.word_to_num(award_number)
                except Exception as e:
                    logger.error('could not convert award number using w2n: ' + str(match.group(Document.award_term_period_number_match_group)))
                    award_number = None

            if award_number:
                period_key = 'award_'+ str(award_number)
            ## if award number not found
            else:
                ## if generic award term, add as award period 1
                if award_title.lower().strip() == 'award term' or award_title.lower().strip() == 'award-term' or award_title.lower().strip() == 'award–term':
                    award_number = 1
                    period_key = 'award_'+ str(award_number)
                ## else, add the award title text found
                else:
                    period_key = str(award_title)
                
            found_period = True

        ## if valid period found, attempt to parse it
        if found_period:
            logger.debug('found pop period!')  
            logger.debug(str(period_key)) 
            if period_key not in periods[Document.dates_key].keys():
                logger.debug('unique period found; attempting to add')

                ## look for the date duration matchgroup. should have both dates
                if match.group(Document.date_duration_match_group):

                    periods[Document.dates_key][period_key] = {'text': match.group(Document.date_duration_match_group)}
                    periods[Document.dates_key][period_key]['date1_text'] =  match.group(Document.date1_match_group)
                    periods[Document.dates_key][period_key]['date2_text'] =  match.group(Document.date2_match_group)
                        

                    ## check for invalid feb 29.. dont want to error on this; just switch the feb 28 instead
                    feb_29_date_pattern = r'Feb(ruary)?\s*\.?\s*29'
                    feb_29_date_re = re.compile(feb_29_date_pattern, re.IGNORECASE)

                    try:
                        if re.search(feb_29_date_re, periods[Document.dates_key][period_key]['date1_text'] ):
                            test = dateutil.parser.parse(periods[Document.dates_key][period_key]['date1_text'])

                    # except ValueError as e:
                    except Exception as e:
                        logger.error('date1: invalid feb 29 date - changing to feb 28')
                        periods[Document.dates_key][period_key]['date1_text'] = periods[Document.dates_key][period_key]['date1_text'].replace('29', '28')

                    try:
                        if re.search(feb_29_date_re, periods[Document.dates_key][period_key]['date2_text'] ):
                            test = dateutil.parser.parse(periods[Document.dates_key][period_key]['date2_text'])

                    except Exception as e:
                        logger.error('date2: invalid feb 29 date - changing to feb 28')
                        periods[Document.dates_key][period_key]['date2_text'] = periods[Document.dates_key][period_key]['date2_text'].replace('29', '28')

                    ## attempt to convert date text to datetime objects
                    try:
                        periods[Document.dates_key][period_key]['date1'] = dateutil.parser.parse(periods[Document.dates_key][period_key]['date1_text'])
                        periods[Document.dates_key][period_key]['date2'] = dateutil.parser.parse(periods[Document.dates_key][period_key]['date2_text'])
                    except Exception as e: 
                        logger.error('could not parse dates for : ' + str(period_key))
                        logger.error( str(e))
                        logger.error(type(e).__name__)
                        del periods[Document.dates_key][period_key]
                        continue

                    ## get duration by subtracting dates
                    try:
                        periods[Document.dates_key][period_key]['duration'] =  periods[Document.dates_key][period_key]['date2'] - periods[Document.dates_key][period_key]['date1']
                        periods[Document.dates_key][period_key]['days'] =  periods[Document.dates_key][period_key]['duration'].days
                    except Exception as e:
                        logger.error('could not read DATE duration correctly for: ' + str(period_key))
                        del periods[Document.dates_key][period_key]
                        logger.error( str(e))
                        logger.error(type(e).__name__)
                        continue
            
                else:
                    logger.warning('could not add period... duration match group not found')

            else:
                logger.warning('not overwriting duplicate period of performance period: ' + str(period_key))

    return periods

def scrape_pop_days_multiplier_words(periods, text, pop_lines_added, pop_lines_added_indices):
    """
    format 3 for finding period of performance in text
    e.g. four (4) twelve (12) month option periods
    """
    multiplier_words_pattern = r'((((one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|twenty[‐–-]one|twenty[‐–-]two|twenty[‐–-]three|twenty[‐–-]four)?(\s+)?(\(?\d+\)?)?))\s*,?(\s+)?((one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|twenty[‐–-]one|twenty[‐–-]two|twenty[‐–-]three|twenty[‐–-]four)?(\s+)?(\(?\d+\)?)?))\s*[‐–-]*(\s+)?((days?)|(months?)|(years?))\s*((base\s*(period)?)|(option\s*(period)?)|(award(-?|\s*)terms))'
    multiplier_words_re = re.compile(multiplier_words_pattern, re.IGNORECASE)

    number1_match_group = 6
    number1_second_match_group = 4

    number2_match_group = 11
    number2_second_match_group = 9
    
    days_match_group = 14
    months_match_group = 15
    years_match_group = 16
    
    base_period_match_group = 15
    option_period_match_group = 17
    award_term_match_group = 19

    base_period_match_group = 18
    option_period_match_group = 20
    award_term_match_group = 22

    options_all_key = 'options'
    award_term_key = 'award'
    additional_key = 'additional'

    periods[Document.mult_words_key] = {}

    last_period_added = {}

    ## loop through regex format matches
    for match_ind, match in enumerate(re.finditer(multiplier_words_re, text)):
        
        found_period = False

        period_key = ''

        ## check for base period, option periods, and award periods
        if match.group(base_period_match_group):
            logger.debug('found base period')
            period_key = Document.base_key
            found_period = True
            
        elif match.group(option_period_match_group):
            option_title = match.group(option_period_match_group)
            logger.debug(str(option_title))
            
            period_key = options_all_key
            found_period = True

        elif match.group(award_term_match_group):
            award_title = match.group(award_term_match_group)
            logger.debug(str(award_title))
            
            period_key = award_term_key
            found_period = True

        if found_period:
            logger.debug('found pop period!')  
            logger.debug(str(period_key))

            ## existence of number1_match_group says that we need multiplier
            number1 = None
            if match.group(number1_match_group):
                try:
                    number1_str_stripped = match.group(number1_match_group).strip('()')
                    number1 = int(number1_str_stripped)
                except Exception as e:
                    logger.error('number ONE cannot be converted to int for: ' + str(period_key))
                    logger.error( str(e))
                    logger.error(type(e).__name__)
                    continue

            elif match.group(number1_second_match_group):
                try:
                    number1_str_stripped = match.group(number1_second_match_group).strip('()')
                    number1 = w2n.word_to_num(number1_str_stripped)
                except Exception as e:
                    logger.error('number ONE (word version) cannot be converted to int for: ' + str(period_key))
                    logger.error( str(e))
                    logger.error(type(e).__name__)
                    continue

            ## number2 is required for match
            number2 = None
            if match.group(number2_match_group):
                try:
                    number2_str_stripped = match.group(number2_match_group).strip('()')
                    number2 = int(number2_str_stripped)
                except Exception as e:
                    logger.error('number TWO cannot be converted to int for: ' + str(period_key))
                    logger.error( str(e))
                    logger.error(type(e).__name__)
                    continue

            elif match.group(number2_second_match_group):
                try:
                    number2_str_stripped = match.group(number2_second_match_group).strip('()')
                    number2 = w2n.word_to_num(number2_str_stripped)
                except Exception as e:
                    logger.error('number TWO (word version) cannot be converted to int for: ' + str(period_key))
                    logger.error( str(e))
                    logger.error(type(e).__name__)
                    continue

            if number2:
                ## check if multiple option periods are mentioned
                ## if they are mentioned in consecutive lines, they are probably referring to separate, unique periods (not repeated)
                if period_key == options_all_key:
                    if period_key in periods[Document.mult_words_key].keys():
                        found_prev = False
                        found_cur = False
                        curr_period_index = None
                        last_period_index_added = None
                        ## check wording, line index, etc.
                        cumulative_text = ''
                        for i, line in enumerate(pop_lines_added):
                            cumulative_text += ' '
                            # cumulative_text += line.get_text().replace('\n', ' ')
                            cumulative_text += line.replace('\n', ' ')
                            if not found_prev and last_period_added['text'] in cumulative_text:
                                logger.debug('found prev')
                                logger.debug(str(cumulative_text.encode("utf-8")))
                                last_period_index_added = i
                                found_prev = True
                            if not found_cur and match.group(0).replace('\n', ' ') in cumulative_text:
                                logger.debug('found cur')
                                logger.debug(str(cumulative_text.encode("utf-8")))
                                curr_period_index = i
                                found_cur = True

                            if found_cur and found_prev:
                                break

                        if not found_cur or not found_prev:
                            logger.debug(str(cumulative_text.encode("utf-8")))
                            logger.debug('prev= ' + str(last_period_added['text'].encode("utf-8")))
                            logger.debug('cur= ' + str(str(match.group(0)).encode("utf-8")))
                            logger.error('couldnt find prev or curr pop line index: prev= ' + str(found_prev) + '; cur= ' + str(found_cur))
                            continue
                        else:
                            logger.debug('found both current and prev match line indices')

                        if (pop_lines_added_indices[curr_period_index] - pop_lines_added_indices[last_period_index_added] <= 1) and (pop_lines_added_indices[curr_period_index] - pop_lines_added_indices[last_period_index_added] >= 0):
                            logger.debug('cur index is next index; add additional key')
                            period_key = additional_key
                        else:
                            logger.debug('cur is not next line: ' +str (pop_lines_added_indices[curr_period_index] - pop_lines_added_indices[last_period_index_added]))
                        
                    
                ## dont add repeated mentions throughout the doc
                if period_key not in periods[Document.mult_words_key].keys():

                    periods[Document.mult_words_key][period_key] = {'text': match.group(0)}
                    periods[Document.mult_words_key][period_key]['number1'] =  number1
                    periods[Document.mult_words_key][period_key]['number2'] =  number2

                    ## if both numbers exist, multiply to get the duration number, else use number2
                    duration_number = None
                    if number1:
                        duration_number = number1 * number2
                    else:
                        duration_number = number2

                    periods[Document.mult_words_key][period_key]['total_duration_number'] = duration_number

                    ## try to convert the duration period to a datetime timdelta object
                    try:
                        if match.group(days_match_group):
                            periods[Document.mult_words_key][period_key]['unit'] = 'days'
                            periods[Document.mult_words_key][period_key]['duration'] = datetime.timedelta(days=duration_number)
                        elif match.group(months_match_group):
                            periods[Document.mult_words_key][period_key]['unit'] = 'months'
                            periods[Document.mult_words_key][period_key]['duration'] = datetime.timedelta(days=round(duration_number*30.41))
                        elif match.group(years_match_group):
                            periods[Document.mult_words_key][period_key]['unit'] = 'years'
                            periods[Document.mult_words_key][period_key]['duration'] = datetime.timedelta(days=duration_number*365)
                    except Exception as e:
                        logger.error('could not create timedelta for : ' + str(period_key))
                        del periods[Document.mult_words_key][period_key]
                        logger.error( str(e))
                        logger.error(type(e).__name__)
                        continue
                        
                    try:
                        periods[Document.mult_words_key][period_key]['days'] = periods[Document.mult_words_key][period_key]['duration'].days
                    except Exception as e:
                        logger.error('could not read MULT duration correctly for: ' + str(period_key))
                        del periods[Document.mult_words_key][period_key]
                        logger.error( str(e))
                        logger.error(type(e).__name__)
                        continue
                        
                    last_period_added = periods[Document.mult_words_key][period_key]

                else:
                    logger.warning('not overwriting duplicate period of performance period: ' + str(period_key))

    return periods


def scrape_pop_days_catch_all(periods, text):
    """
    catch all format for period of performance days extraction
    e.g. 12 months
    """
    
    periods[Document.catch_all_key] = {}

    duration_number_match_group = 2
    days_match_group = 8
    months_match_group = 9
    years_match_group = 10

    ## add all catch all format matches
    catch_all_num = 1
    for match_ind, match in enumerate(re.finditer(Document.length_of_time_words_pattern, text.replace('(','').replace(')', ''))):
        if match.group(duration_number_match_group):
            try:
                duration_number = w2n.word_to_num(match.group(duration_number_match_group))
            except:
                logger.error('duration number cannot be converted to int in catch all')
                continue

            periods[Document.catch_all_key][catch_all_num] = {'text': match.group(0)}
            periods[Document.catch_all_key][catch_all_num]['number'] =  duration_number

            try:
                if match.group(days_match_group):
                    periods[Document.catch_all_key][catch_all_num]['unit'] = 'days'
                    periods[Document.catch_all_key][catch_all_num]['duration'] = datetime.timedelta(days=duration_number)
                elif match.group(months_match_group):
                    periods[Document.catch_all_key][catch_all_num]['unit'] = 'months'
                    periods[Document.catch_all_key][catch_all_num]['duration'] = datetime.timedelta(days=round(duration_number*30.41))
                elif match.group(years_match_group):
                    periods[Document.catch_all_key][catch_all_num]['unit'] = 'years'
                    periods[Document.catch_all_key][catch_all_num]['duration'] = datetime.timedelta(days=duration_number*365)
            except:
                    logger.error('could not create timedelta in catch all ')
                    del periods[Document.catch_all_key][catch_all_num]
                    continue
                
            try:
                periods[Document.catch_all_key][catch_all_num]['days'] = periods[Document.catch_all_key][catch_all_num]['duration'].days
            except:
                logger.error('could not read WORD duration correctly in catch all ')
                del periods[Document.catch_all_key][catch_all_num]
                continue

            catch_all_num += 1
        
        else:
            logger.warning('could not add period... duration match group not found')

    return periods


def get_period_of_performance_length_of_time(text, pop_lines_added, pop_lines_added_indices, multproc_results=None):
    """
    uses formats to extract period of performance periods into a dictionary
    calls each format extraction separately 
    """
    try:
        periods = {}
        
        ## format 1
        periods = scrape_pop_days_duration_words(periods, text)
        ## format 2
        periods = scrape_pop_days_dates(periods, text)
        ## format 3
        periods = scrape_pop_days_multiplier_words(periods, text, pop_lines_added, pop_lines_added_indices)
        ## catch all format
        periods = scrape_pop_days_catch_all(periods, text)
        logger.debug(str(str(periods).encode("utf-8")))

        if multproc_results:
            multproc_results.put(periods)

        return periods

    except Exception as e:
        logger.error('ERROR PARSING POP DAYS')
        logger.error(type(e).__name__)
        logger.error( str(e))

        periods = {}
        if multproc_results:
            multproc_results.put(periods)

        return periods
                        
def get_total_period_of_performance_days(pop_dict):
    """
    goes through period of performance periods dict to get total days
    generally, uses format with most total days found
    adds base, options, and award periods from other formats if not included in format used
    uses max duration from catch all if needed
    """

    all_days = []
    includes_base = [False,False,False]
    includes_options = [False,False,False]
    includes_awards = [False,False,False]

    base_days = 0
    options_days = [0,0,0]
    awards_days = [0,0,0]

    ## format 2
    dates_days = 0
    for period_key in pop_dict[Document.dates_key].keys():
        days_to_add = pop_dict[Document.dates_key][period_key]['days']
        dates_days += days_to_add
        if period_key == Document.base_key:
            base_days = days_to_add
            includes_base[0] = True

        elif 'option' in period_key.lower():
            options_days[0] += days_to_add
            includes_options[0] = True
        else:
            awards_days[0] += days_to_add
            includes_awards[0] = True

    all_days.append(dates_days)

    ## format 1
    dur_days = 0
    for period_key in pop_dict[Document.duration_words_key].keys():

        # #### TEMP ####
        # if period_key == Document.base_key:
        #     pop_dict[Document.duration_words_key][period_key]['days'] = 1000
        # ####

        days_to_add = pop_dict[Document.duration_words_key][period_key]['days']
        dur_days += days_to_add
        if period_key == Document.base_key:
            base_days = days_to_add
            includes_base[1] = True

        elif 'option' in period_key.lower():
            options_days[1] += days_to_add
            includes_options[1] = True
        else:
            awards_days[1] += days_to_add
            includes_awards[1] = True

    all_days.append(dur_days)

    ## format 3
    mult_days = 0
    for period_key in pop_dict[Document.mult_words_key].keys():

        # #### TEMP ####
        # if period_key == Document.base_key:
        #     pop_dict[Document.mult_words_key][period_key]['days'] = 3000
        # ####

        days_to_add = pop_dict[Document.mult_words_key][period_key]['days']
        mult_days += days_to_add
        if period_key == Document.base_key:
            base_days = days_to_add
            includes_base[2] = True
        elif 'option' in period_key.lower():
            options_days[2] += days_to_add
            includes_options[2] = True
        else:
            awards_days[2] += days_to_add
            includes_awards[2] = True
            
    all_days.append(mult_days)

    ## catch all format
    catch_all_days = 0
    for period_key in pop_dict[Document.catch_all_key].keys():
        if pop_dict[Document.catch_all_key][period_key]['days'] > catch_all_days:
            catch_all_days = pop_dict[Document.catch_all_key][period_key]['days']
    all_days.append(catch_all_days)
  
    ## choose format with most total days
    max_index = all_days.index(max(all_days))
    days = all_days[max_index]

    if days == 0:
        days = ''
        logger.debug('pop days == 0; setting to empty string')
    else:
        if max_index == 0:
            logger.debug('added days from DATES')
        elif max_index == 1:
            logger.debug('added days from DUR WORDS')
        elif max_index == 2:
            logger.debug('added days from MULT WORDS')
        elif max_index == 3:
            logger.debug('added max days from CATCH ALL')

        ## check if base, option, and award periods were included
        ## if not, add them to the total days from other formats
        if max_index != 3 :
        
            if not includes_base[max_index]:
                ## add base from other format
                logger.debug('format ' + str(max_index) + ' did not include BASE; attempting to add it - base days = ' + str(base_days))
                days += base_days
        
            if not includes_options[max_index]:
                ## add options from other format
                logger.debug('format ' + str(max_index) + ' did not include any OPTIONS; attempting to add it - max total options days = ' + str(max(options_days)))
                days += max(options_days)

            if not includes_awards[max_index]:
                ## add awards from other format
                logger.debug('format ' + str(max_index) + ' did not include any AWARDS; attempting to add it - max total awards days = ' + str(max(awards_days)))
                days += max(awards_days)
            
    return days


def extract_period_of_performance(pop_topic):
    """
    first pass clean of period of performance topic
    looks for dates, durations, and periods
    """

    logger.debug('extracting period of performance from period of performance topic')

    lines = pop_topic.line_elements
    line_indices = pop_topic.line_element_indices

    pop_time_words = ['month','day','year']
    date_regexes = []
    
    date_regexes.append(re.compile( r'\b(\d{2}|\d)[\/-](\d{2}|\d)[\/-]?(\d{4}|\d{2})|(\d{4}|\d{2})[\/-](\d{2}|\d)[\/-](\d|\d{2})\b'))
    date_regexes.append(re.compile( r'\b((Mon|Tue|Wed|Thu|Fri|Sat|Sun)[a-z]*)*[\ ,-]*(\d|\d{2})*(st|nd|rd|th)*[\ ,-]*(Jan(uary)?|Feb(ruary)?|Mar(ch)?|May|Apr(il)?|Jul(y)|Jun(e)?|Aug(ust)?|Oct(ober)|Sep(tember)?|Nov(ember)?|Dec(ember)?)[\ ,]*(\d|\d{2}|\d{4})*(st|nd|rd|th)*([\ ,])*\'*(\d{2}|\d{4})*\b', re.IGNORECASE))
    date_regexes.append(re.compile( r'\b(19|20)[0-9]{2}\b'))

    period_pattern = r'((option\s*(period)\s*((\d+)|(one|two|three|four|five|six|seven|eight|nine|ten))*)|(base\s*(period)))'
    period_re = re.compile(period_pattern, re.IGNORECASE)

    additional_pattern_1 = r'option'
    addition_re_1 = re.compile(additional_pattern_1, re.IGNORECASE)

    additional_pattern_2 = r'base'
    addition_re_2 = re.compile(additional_pattern_2, re.IGNORECASE)
    
    pop_regexes = []
    pop_text = ''
    for word in pop_time_words:
        new_regex = re.compile(word +'s?')
        pop_regexes.append(new_regex)

    lines_added=[]
    lines_added_indices = []
    for line_index, line in enumerate(lines):
        logger.warning(str(line_indices[line_index]) + ': ' + str(line.get_text().encode("utf-8")))
        # logger.warning()
        text=line.get_text()
        for pop_regex in pop_regexes:
            if re.search(pop_regex, text):
                if line not in lines_added:
                    if pop_text != '':
                        pop_text += '\n'
                    try:
                        if (lines[line_index - 1] not in lines_added) \
                            and (line_indices[line_index-1] == line_indices[line_index] - 1): ## this ensures that the lines actually come directly before the line being added in the document
                            
                            logger.debug('adding line before: ' + str(lines[line_index - 1].get_text().encode("utf-8")))
                            pop_text += lines[line_index - 1].get_text() 
                            pop_text += ' '
                            lines_added.append(lines[line_index - 1])
                            lines_added_indices.append(line_indices[line_index-1])

                    except (IndexError):
                        logger.warning('could not grab text before pop regex match: ' + str(text.encode("utf-8")))
                    
                    logger.debug('adding line: ' + str(text.encode("utf-8")))
                    pop_text += text
                    lines_added.append(line)
                    lines_added_indices.append(line_indices[line_index])

        for date_regex in date_regexes:
            if re.search(date_regex, text):
                if line not in lines_added:
                    if pop_text != '':
                        pop_text += '\n'
                    try:
                        if (lines[line_index - 1] not in lines_added) \
                            and (line_indices[line_index-1] == line_indices[line_index] - 1): ## this ensures that the lines actually come directly before the line being added in the document
                            
                            logger.debug('adding line before: ' + str(lines[line_index - 1].get_text().encode("utf-8")))
                            pop_text += lines[line_index - 1].get_text() 
                            pop_text += ' '
                            lines_added.append(lines[line_index - 1])
                            lines_added_indices.append(line_indices[line_index-1])

                    except (IndexError):
                        logger.warning('could not grab text before date: ' + text)
                    
                    logger.debug('adding line: ' + str(text))
                    pop_text += text
                    lines_added.append(line)
                    lines_added_indices.append(line_indices[line_index])

        add_line_additional_search = False
        if line not in lines_added:
            if re.search(period_re, text):
                add_line_additional_search = True

            elif re.search(addition_re_1, text):
                add_line_additional_search = True

            elif re.search(addition_re_2, text):
                add_line_additional_search = True

            if add_line_additional_search:
                if pop_text != '':
                    pop_text += '\n'
                logger.debug('adding line from additional regex match: ' + str(text))
                pop_text += text
                lines_added.append(line)
                lines_added_indices.append(line_indices[line_index])

                   
    return pop_text, lines_added, lines_added_indices

def parse_text_for_summary(document, cutoff_num_sentences):
    """
    compiles text to summarize based on priotized topics and cutoff_num_sentences parameter
    """
    
    section_to_add_index = 0
    keep_adding_text = True
    while keep_adding_text:
        # num_words_to_summarize = len(re.findall(r'[a-zA-Z]\w*', document.text_to_summarize))
        nlp = spacy.lang.en.English()
        nlp.add_pipe(nlp.create_pipe('sentencizer'))
        logger.debug('text to summarize so far: ' + str(str([document.text_to_summarize]).encode("utf-8")))
        nlp_doc = nlp(document.text_to_summarize)
        num_sentences_to_summarize = len(list(nlp_doc.sents))

        # if ( num_words_to_summarize <= config.CUTOFF_NUM_WORDS_PRE_SUMMARY):
        if (num_sentences_to_summarize <= cutoff_num_sentences):
            # logger.debug('text_to_summarize num words <= config.CUTTOFF: ' + str(num_words_to_summarize) + '<=' + str(config.CUTOFF_NUM_WORDS_PRE_SUMMARY))
            logger.debug('text_to_summarize num sentences <= config.CUTTOFF: ' + str(num_sentences_to_summarize) + '<=' + str(cutoff_num_sentences))

            if section_to_add_index < len(document.sections_to_summarize_by_priority):
                logger.debug('section_to_add_index < len(sections_to_add): '+ str(section_to_add_index) + '<' + str(len(document.sections_to_summarize_by_priority)))
                logger.debug('attempting to add ' + str(document.sections_to_summarize_by_priority[section_to_add_index]))
                text_added = document.add_text_to_summarize(document.topics_dict[document.sections_to_summarize_by_priority[section_to_add_index]])
                if not text_added:
                    logger.debug('could not add topic text because topic text is empty string')
                section_to_add_index += 1
            ## this means we do not have enough text to summarize AND we are out of sections to add; therefore, add entire doc
            else:
                logger.debug('section_to_add_index >= len(sections_to_add): '+ str(section_to_add_index) + '>=' + str(len(document.sections_to_summarize_by_priority)))
                logger.debug('adding ALL TEXT')
                all_text_topic = Topic('ALLTEXT')
                all_text_topic.text = document.all_text

                ###############################################################################################
                # ## DONT INCLUDE TEXT THAT IS ALREADY BEING ADDED TO TEXT TO SUMMARIZE
                for topic_name in  document.sections_to_summarize_by_priority:
                    for section_ind, section in enumerate(document.topics_dict[topic_name].sections):
                        if section.text in all_text_topic.text:
                            all_text_topic.text = all_text_topic.text.replace(section.text, '')
                            logger.debug('REMOVE REPEATED SECTION TEXT in SECTION ' + str (section_ind) + ' OF TOPIC ' + str(topic_name) + ' FROM ALLTEXT TOPIC:: ' + str(section.text))
                    for custom_line in document.topics_dict[topic_name].custom_line_elements_added:
                        if custom_line.text in all_text_topic.text:
                            all_text_topic.text = all_text_topic.text.replace(custom_line.text, '')
                            logger.debug('REMOVE REPEATED CUSTOM LINE TEXT OF TOPIC ' + str(topic_name) + ' FROM ALLTEXT TOPIC:: ' + str (custom_line.text))
                ###############################################################################################
                document.add_text_to_summarize(all_text_topic)
                keep_adding_text = False      
        else:
            # logger.debug('text_to_summarize num words > config.CUTTOFF: ' + str(num_words_to_summarize) + '>' + str(config.CUTOFF_NUM_WORDS_PRE_SUMMARY))
            logger.debug('text_to_summarize num sentences > config.CUTTOFF: ' + str(num_sentences_to_summarize) + '>' + str(cutoff_num_sentences))
            keep_adding_text = False

def parse_pdf_file(input_file_path, reportables_file_path, clause_depth=3, font_adjust_percentage=0.8, use_left_indent=True):
    """
    calls ContractBot to parse the pdf file
    sectionizes doc by whitespace, finds regex matches, and applies ML cluster matches
    """

    logger.debug("Setting Config Values...")
    logger.debug('reportables_path= ' + str(reportables_file_path))
    logger.debug('clause_depth= ' + str(clause_depth))
    logger.debug('font_adjust_percentage= ' + str(font_adjust_percentage))
    logger.debug('use_left_indent= ' + str(use_left_indent))
    config = pdfprocessor.get_pdf_config(clause_depth = clause_depth, 
                                        reportables_path = reportables_file_path, 
                                        html_template=None, 
                                        font_adjust_percent=font_adjust_percentage, 
                                        use_left_indent=use_left_indent
                                     )
    
    
    # config.FontAdjustPercent = font_adjust_percentage
    # config.UseLeftIndent = use_left_indent

    logger.debug("Creating ContractBot.ContractBotPDFConverter instance")
    pconbot = pdfprocessor.get_contract_bot_pdf_converter(config=config, filepaths_list=[input_file_path])

    # logger.debug("Adding files for processing...")
    # pconbot.AddFile(input_file_path)
    
    logger.debug("Converting...Please Hold")
    pconbot.Convert()
    logger.debug("CBot Done!")

    parsed_file_path = input_file_path + ".parsed.html"
    return parsed_file_path

# def parse_pdf_file(input_file_path, reportables_file_path, clause_depth=3, font_adjust_percentage=0.8, use_left_indent=True):

#     config = pdfprocessor.get_pdf_config(clause_depth = clause_depth, 
#                                         reportables_path = reportables_file_path
#                                      )
#     logger.debug("Setting Config Values...")
#     logger.debug('font_adjust_percentage= ' + str(font_adjust_percentage))
#     logger.debug('use_left_indent= ' + str(use_left_indent))
#     config.FontAdjustPercent = font_adjust_percentage
#     config.UseLeftIndent = use_left_indent

#     logger.debug("Creating ContractBot.ContractBotPDFConverter instance")
#     pconbot = pdfprocessor.get_contract_bot_pdf_converter(config)

#     logger.debug("Adding files for processing...")
#     pconbot.AddFile(input_file_path)
    
#     logger.debug("Converting...Please Hold")
#     pconbot.Convert()
#     logger.debug("CBot Done!")

#     parsed_file_path = input_file_path + ".parsed.html"
#     return parsed_file_path

# def parse_pdf_file(input_file_path, reportables_file_path):
#     logger.debug("Creating ContractBot.ContractBotPDFConverter instance")
#     pconbot = ContractBotPDFConverter()
#     logger.debug("Adding files for processing...")
#     pconbot.AddFile(input_file_path)
#     logger.debug("Setting Reportables...")
#     pconbot.ReportsFile = reportables_file_path
#     logger.debug("Converting...Please Hold")
#     pconbot.Convert()
#     logger.debug("Done! - opening page")
#     parsed_file_path = input_file_path + ".parsed.html"

    # return parsed_file_path

