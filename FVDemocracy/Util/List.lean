/-!
# Lemmas about lists

General facts about `List.eraseDups` and sums over lists used by the Alaska and RCV
formalizations.
-/

namespace List

theorem eraseDups_eq_nil_iff {α : Type} [BEq α] {l : List α} : l.eraseDups = [] ↔ l = [] := by
  cases l with
  | nil => rfl
  | cons a as => simp [List.eraseDups_cons]

/-- Two members of a list with at most one distinct element are equal. -/
theorem eq_of_mem_of_eraseDups_length_le_one {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    {c d : α} (hl : l.eraseDups.length ≤ 1) (hc : c ∈ l) (hd : d ∈ l) : c = d := by
  cases l with
  | nil => simp at hc
  | cons a as =>
    rw [List.eraseDups_cons, List.length_cons] at hl
    have hnil : (as.filter (fun b => !b == a)).eraseDups = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hall : ∀ x ∈ a :: as, x = a := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · cases hxa : x == a with
        | true => exact eq_of_beq hxa
        | false =>
          have hmem : x ∈ as.filter (fun b => !b == a) := List.mem_filter.mpr ⟨hx, by simp [hxa]⟩
          rw [eraseDups_eq_nil_iff.mp hnil] at hmem
          exact absurd hmem List.not_mem_nil
    rw [hall c hc, hall d hd]

theorem mem_of_mem_eraseDups {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : a ∈ l.eraseDups) : a ∈ l := by
  suffices ∀ n (l : List α), l.length ≤ n → a ∈ l.eraseDups → a ∈ l from
    this _ _ (Nat.le_refl _) h
  intro n
  induction n with
  | zero => intro l hl h; simp_all
  | succ n ih =>
    intro l hl h
    cases l with
    | nil => simp at h
    | cons b bs =>
      rw [List.eraseDups_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · have hlen : (bs.filter fun x => !x == b).length ≤ n :=
          Nat.le_trans (List.length_filter_le _ _) (by simpa using hl)
        exact List.mem_cons_of_mem _ (List.mem_filter.mp (ih _ hlen h)).1

theorem mem_eraseDups_of_mem {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : a ∈ l) : a ∈ l.eraseDups := by
  suffices ∀ n (l : List α), l.length ≤ n → a ∈ l → a ∈ l.eraseDups from
    this _ _ (Nat.le_refl _) h
  intro n
  induction n with
  | zero => intro l hl h; simp_all
  | succ n ih =>
    intro l hl h
    cases l with
    | nil => simp at h
    | cons b bs =>
      rw [List.eraseDups_cons]
      by_cases hab : a = b
      · subst hab
        exact List.mem_cons_self
      · have hlen : (bs.filter fun x => !x == b).length ≤ n :=
          Nat.le_trans (List.length_filter_le _ _) (by simpa using hl)
        have has : a ∈ bs := by simpa [hab] using h
        exact List.mem_cons_of_mem _ (ih _ hlen (List.mem_filter.mpr ⟨has, by simpa using hab⟩))

theorem mem_eraseDups {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    a ∈ l.eraseDups ↔ a ∈ l :=
  ⟨mem_of_mem_eraseDups, mem_eraseDups_of_mem⟩

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  suffices ∀ n (l : List α), l.length ≤ n → l.eraseDups.Nodup from this _ _ (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro l hl; simp_all
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp
    | cons b bs =>
      have hlen : (bs.filter fun x => !x == b).length ≤ n :=
        Nat.le_trans (List.length_filter_le _ _) (by simpa using hl)
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨fun hb => ?_, ih _ hlen⟩
      have := List.mem_filter.mp (mem_of_mem_eraseDups hb)
      simp at this

/-- A list has two different members exactly when it has at least two distinct elements. -/
theorem exists_ne_iff_two_le_length_eraseDups {α : Type} [BEq α] [LawfulBEq α] {l : List α} :
    (∃ a ∈ l, ∃ b ∈ l, a ≠ b) ↔ 2 ≤ l.eraseDups.length := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact Nat.le_of_not_lt fun hlt => hab (eq_of_mem_of_eraseDups_length_le_one (by omega) ha hb)
  · intro h
    have hnd := nodup_eraseDups l
    match hl : l.eraseDups, hnd with
    | [], _ => simp [hl] at h
    | [_], _ => simp [hl] at h
    | a :: b :: rest, hnd =>
      have hmem : ∀ x ∈ a :: b :: rest, x ∈ l := fun x hx => mem_of_mem_eraseDups (hl ▸ hx)
      refine ⟨a, hmem a (by simp), b, hmem b (by simp), fun hab => ?_⟩
      subst hab
      exact (List.nodup_cons.mp hnd).1 List.mem_cons_self

/-- Removing a member of a list makes it shorter. -/
theorem length_erase_lt_of_mem {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : a ∈ l) : (l.erase a).length < l.length := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    rw [List.erase_cons]
    cases hb : b == a
    · rw [if_neg Bool.false_ne_true]
      have ha : a ∈ l := by
        rcases List.mem_cons.mp h with rfl | ha
        · exact absurd (beq_self_eq_true a) (by rw [hb]; exact Bool.false_ne_true)
        · exact ha
      exact Nat.succ_lt_succ (ih ha)
    · rw [if_pos rfl]
      exact Nat.lt_succ_self _

theorem le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp
      omega

/-- Counting the members that satisfy `p` gives the same number on two lists of the same length
when `p` holds at the same positions. -/
theorem countP_eq_of_forall_mem_zip {α β : Type} {l : List α} {l' : List β}
    (hlen : l.length = l'.length) {p : α → Bool} {p' : β → Bool}
    (h : ∀ q ∈ l.zip l', p q.1 = p' q.2) : l.countP p = l'.countP p' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a l ih => cases l' with
    | nil => simp at hlen
    | cons a' l' =>
      have ha : p a = p' a' := h (a, a') (by simp)
      have ht := ih (by simpa using hlen) fun q hq => h q (by simp [hq])
      simp only [List.countP_cons, ha, ht]

/-- Filtering two lists of the same length by predicates that hold at the same positions keeps
the same pairs of members. -/
theorem zip_filter_eq_of_forall_mem_zip {α β : Type} {l : List α} {l' : List β}
    (hlen : l.length = l'.length) {p : α → Bool} {p' : β → Bool}
    (h : ∀ q ∈ l.zip l', p q.1 = p' q.2) :
    (l.filter p).zip (l'.filter p') = (l.zip l').filter fun q => p q.1 := by
  induction l generalizing l' with
  | nil => simp
  | cons a l ih => cases l' with
    | nil => simp at hlen
    | cons a' l' =>
      have ha : p a = p' a' := h (a, a') (by simp)
      have ht := ih (by simpa using hlen) fun q hq => h q (by simp [hq])
      cases hpa : p a <;> simp [hpa, ← ha, ht]

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]; omega

theorem sum_map_ite_eq_count {α : Type} [DecidableEq α] (l : List α) (a : α) :
    (l.map fun x => if x = a then 1 else 0).sum = l.count a := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.count_cons, ih]; omega

/-- Summing over a list without duplicates, 1 for `a` and 0 for every other member, gives 1. -/
theorem sum_map_ite_eq_one {α : Type} [DecidableEq α] {l : List α} (hl : l.Nodup) {a : α}
    (ha : a ∈ l) : (l.map fun x => if x = a then 1 else 0).sum = 1 := by
  rw [sum_map_ite_eq_count, List.Nodup.count hl, if_pos ha]

end List
