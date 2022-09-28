import tactic

namespace blueprint

lemma first_test (h : false) : true :=
begin
  tauto,
end

lemma second_test (h : false) : true :=
begin
  tauto,
end

end blueprint