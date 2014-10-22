
procedure proc3 (ARG2: in out Integer) is
   procedure P1 (ARG: in out Integer) is
   begin
      ARG := ARG+1;
   end;
begin
   P1(ARG2);
end;
