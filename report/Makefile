pdf: dvi
	dvips -o report.ps -Ppdf -G0 -t letter report.dvi
	ps2pdf -dMaxSubsetPct=100 -dSubsetFonts=true -dEmbedAllFonts=true report.ps report.pdf

dvi:
	latex report
	latex report
# uncomment if you cite things
#	bibtex report
#	latex report

clean:
	rm -f text/*~
	rm -f bib/*~
	rm -f figs/*~
	rm -f *~
	rm -f *.aux *.bbl *.blg *.log
