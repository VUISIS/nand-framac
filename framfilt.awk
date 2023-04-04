BEGIN {
  print_data = 0;
  }
/^.wp. .Failure./ { print_data=1; print $0; next;}
/^.wp. Proved/ { print_data=1; print $0; next;}
/^.wp. .*alpha_0/ { print_data=1; print $0; next;}
/^ .*/ { if (print_data == 1) { print $0;} next;}
/^[^ ]/ { print_data=0; next;}
