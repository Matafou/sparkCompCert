
procedure proc2 (ARG: in out Integer; ARG2: in Boolean) is
   N : Boolean := True;
   M: Integer := 27;

   procedure P1 (ARG: in out Integer; ARG2: in Boolean) is
      N : Integer := 3;
   begin
      ARG := ARG + N + M;
      if ARG2 and M < 30 then ARG := 23; else ARG := ARG; end if;
   end;
begin
   P1(M,FALSE);
end;
