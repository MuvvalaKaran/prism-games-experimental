################################################
#  NB: This Makefile is designed to be called  #
#      from the main PRISM Makefile. It won't  #
#      work on its own because it needs        #
#      various options to be passed in         #
################################################

.SUFFIXES: .o .c .cc

# Reminder: $@ = target, $* = target without extension, $< = dependency

THIS_DIR = common
PRISM_DIR_REL = ../..

JNI_GEN_HEADER_DIR=$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_INCLUDE_DIR)/jni

JAVA_FILES_ALL = $(wildcard *.java iterable/*.java functions/*.java)
JAVA_FILES = $(subst package-info.java,,$(JAVA_FILES_ALL))
CLASS_FILES = $(JAVA_FILES:%.java=$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)/$(THIS_DIR)/%.class)

PRISM_CLASSPATH = "$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)$(CLASSPATHSEP)$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_LIB_DIR)/*"

default: all

all: checks $(CLASS_FILES)

# inhibit building in parallel (-j option)
.NOTPARALLEL:

# Try and prevent accidental makes (i.e. called manually, not from top-level Makefile)
checks:
	@if [ "$(PRISM_SRC_DIR)" = "" ]; then \
	  (echo "Error: This Makefile is designed to be called from the main PRISM Makefile"; exit 1) \
	fi; 

$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)/$(THIS_DIR)/%.class: %.java
	(cd ..; $(JAVAC) $(JFLAGS) -sourcepath $(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_SRC_DIR) -classpath $(PRISM_CLASSPATH) -h $(JNI_GEN_HEADER_DIR) -d $(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR) $(THIS_DIR)/$<)

clean: checks
	@rm -f $(CLASS_FILES)

celan: clean

#################################################
