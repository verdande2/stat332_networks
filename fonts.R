library(ragg)
knitr::opts_chunk$set(dev = "ragg_png")
library(extrafont)
library(extrafontdb)


font_log_filepath = FONT_INFO_LOG

capture.output(
  {
    extrafont::font_import(prompt = FALSE)
    extrafont::loadfonts(device = "win", quiet = FALSE)
  },
  file = "fontslog.log",
  append = FALSE,
  type = c("output", "message")
)


available_font_list <- fonts() # a str vector of all available system fonts

# fonttable() prints out a formatted table of all loaded fonts, locations to their ttf files, full name and other attributes

print(paste0("Succesfully loaded ", length(fonts()), " fonts."))
