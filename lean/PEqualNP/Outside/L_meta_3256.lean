import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    wireValue C x i = x.getD i false := fold_getD_lt _ _ _ h

lemma wires_ge (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    wireValue C x w = false := by
  unfold wireValue
  rw [List.getD_eq_default]
  rw [wires_length]
  exact hw

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    wireValue C x (x.length + j)
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  unfold wireValue
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · simp only [hi, ↓reduceIte]
      rw [hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · simp only [hi, ↓reduceIte]
      rw [List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      (∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases hzero : i - a.length = 0
        · simp only [hzero, List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · have heq : [g.op.eval (g.inputs.map fun i => a.getD i false)].getD (i - a.length) false = false := by
            rw [List.getD_eq_default]
            simp; omega
          rw [heq] at hi
          cases hi

lemma incidenceInput_length {n : ℕ} (X Y : Finset (Fin n)) :
    (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

lemma incidenceInput_getD_lt {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; exact hi)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

lemma incidenceInput_getD_right {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (h1 : n ≤ i) (h2 : i < n + n) :
    (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; exact h1)]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hsub : i - n < n := by omega
  simp [hsub]

lemma wireValue_mono {n : ℕ} (C : Circuit) (hAO : AndOrOnly C) (l : Fin n)
    (X Y : Finset (Fin n)) (hXY : X ⊆ Y) (w : ℕ) :
    wireValue C (incidenceInput X {l}) w = true →
    wireValue C (incidenceInput Y {l}) w = true := by
  unfold wireValue
  rw [wires_eq, wires_eq]
  apply fold_mono C.gates hAO
  · simp [incidenceInput_length]
  · intro i hi
    by_cases h1 : i < n
    · rw [incidenceInput_getD_lt _ _ _ h1] at hi ⊢
      simp only [decide_eq_true_eq] at hi ⊢
      exact hXY hi
    · by_cases h2 : i < n + n
      · rw [incidenceInput_getD_right _ _ _ (by omega) h2] at hi ⊢
        exact hi
      · have hdefX : (incidenceInput X {l}).getD i false = false := by
          rw [List.getD_eq_default]
          rw [incidenceInput_length]; omega
        rw [hdefX] at hi
        cases hi

def actSet (n : ℕ) (C : Circuit) (l : Fin n) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p : Fin n => wireValue C (incidenceInput {p} {l}) w = true

lemma actSet_base_card_le_one {n : ℕ} (C : Circuit) (s : Finset (Fin n)) (l : Fin n)
    (w : ℕ) (hw : w < n + n) (hfalse : wireValue C (incidenceInput sᶜ {l}) w = false) :
    (actSet n C l w).card ≤ 1 := by
  by_cases h1 : w < n
  · have hsub : actSet n C l w ⊆ {⟨w, h1⟩} := by
      intro p hp
      simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [wires_input _ _ _ (by rw [incidenceInput_length]; omega),
        incidenceInput_getD_lt _ _ _ h1] at hp
      simp only [decide_eq_true_eq, Finset.mem_singleton] at hp ⊢
      exact hp.symm
    calc (actSet n C l w).card ≤ ({⟨w, h1⟩} : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · have hemp : actSet n C l w = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [wires_input _ _ _ (by rw [incidenceInput_length]; omega),
        incidenceInput_getD_right _ _ _ (by omega) hw] at hp
      rw [wires_input _ _ _ (by rw [incidenceInput_length]; omega),
        incidenceInput_getD_right _ _ _ (by omega) hw] at hfalse
      rw [hp] at hfalse
      cases hfalse
    rw [hemp]
    simp

def isOr (op : GateOp) : Bool :=
  match op with
  | GateOp.or => true
  | _ => false

lemma isOr_iff (op : GateOp) : isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOr]

def goodJ (n : ℕ) (C : Circuit) (s : Finset (Fin n)) (l : Fin n) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun j =>
    j < C.size ∧ isOr (gateAt C j).op = true ∧
      wireValue C (incidenceInput sᶜ {l}) (n + n + j) = false ∧
      2 ≤ (actSet n C l (n + n + j)).card

lemma goodJ_mono {n : ℕ} (C : Circuit) (s : Finset (Fin n)) (l : Fin n) (k : ℕ) :
    goodJ n C s l k ⊆ goodJ n C s l (k + 1) := by
  intro j hj
  simp only [goodJ, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma goodJ_step {n : ℕ} (C : Circuit) (s : Finset (Fin n)) (l : Fin n) (k : ℕ)
    (hk : k < C.size) (hop : (gateAt C k).op = GateOp.or)
    (hfalse : wireValue C (incidenceInput sᶜ {l}) (n + n + k) = false)
    (hcard : 2 ≤ (actSet n C l (n + n + k)).card) :
    (goodJ n C s l (k + 1)).card = (goodJ n C s l k).card + 1 := by
  have heq : goodJ n C s l (k + 1) = insert k (goodJ n C s l k) := by
    ext j
    simp only [goodJ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hrest⟩
      by_cases hjk : j = k
      · left; exact hjk
      · right; exact ⟨by omega, hrest⟩
    · rintro (rfl | ⟨hj, hrest⟩)
      · exact ⟨by omega, hk, (isOr_iff _).mpr hop, hfalse, hcard⟩
      · exact ⟨by omega, hrest⟩
  have hk_not : k ∉ goodJ n C s l k := by
    simp [goodJ]
  rw [heq, Finset.card_insert_of_notMem hk_not]

lemma list_eq_two {α : Type*} (l : List α) (h : l.length = 2) (d : α) :
    l = [l.getD 0 d, l.getD 1 d] := by
  match l, h with
  | [a, b], _ => rfl

lemma list_mem_getD_zero {α : Type*} (l : List α) (h : l.length = 2) (d : α) :
    l.getD 0 d ∈ l := by
  match l, h with
  | [a, b], _ => simp

lemma list_mem_getD_one {α : Type*} (l : List α) (h : l.length = 2) (d : α) :
    l.getD 1 d ∈ l := by
  match l, h with
  | [a, b], _ => simp

lemma step_gate_eval {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C) (X : Finset (Fin n))
    (l : Fin n) (k : ℕ) (hk : k < C.size) :
    C.gates[k].inputs.length = 2 ∧
    (∀ i ∈ C.gates[k].inputs, i < n + n + k) ∧
    wireValue C (incidenceInput X {l}) (n + n + k) =
      C.gates[k].op.eval [wireValue C (incidenceInput X {l}) (C.gates[k].inputs.getD 0 0),
                           wireValue C (incidenceInput X {l}) (C.gates[k].inputs.getD 1 0)] := by
  have hk' : k < C.gates.length := hk
  have hlen : C.gates[k].inputs.length = 2 := hAO.2.2 C.gates[k] (List.getElem_mem hk')
  have hrb : ∀ i ∈ C.gates[k].inputs, i < n + n + k := by
    intro i hi
    have := hAO.2.1 k hk' i
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at this
    exact this hi
  refine ⟨hlen, hrb, ?_⟩
  have heq := wires_gate C (incidenceInput X {l}) k hk'
  rw [incidenceInput_length] at heq
  rw [heq]
  have h0 : C.gates[k].inputs.getD 0 0 < n + n + k := hrb _ (list_mem_getD_zero _ hlen 0)
  have h1 : C.gates[k].inputs.getD 1 0 < n + n + k := hrb _ (list_mem_getD_one _ hlen 0)
  have hin : C.gates[k].inputs = [C.gates[k].inputs.getD 0 0, C.gates[k].inputs.getD 1 0] :=
    list_eq_two _ hlen 0
  conv_lhs => rw [hin]
  simp only [List.map_cons, List.map_nil, rd, h0, h1, ↓reduceIte]
  rfl

lemma biUnion_actSet_bound {n : ℕ} (C : Circuit) (hAO : IsAO2 (n + n) C)
    (s : Finset (Fin n)) (l : Fin n) :
    ∀ k : ℕ, ∀ F : Finset ℕ,
      (∀ w ∈ F, w < n + n + k) →
      (∀ w ∈ F, wireValue C (incidenceInput sᶜ {l}) w = false) →
      (F.biUnion (actSet n C l)).card ≤ F.card + (goodJ n C s l k).card := by
  intro k
  induction k with
  | zero =>
    intro F hFlt hFfalse
    calc (F.biUnion (actSet n C l)).card
        ≤ ∑ w ∈ F, (actSet n C l w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ F, 1 := Finset.sum_le_sum fun w hw =>
          actSet_base_card_le_one C s l w (hFlt w hw) (hFfalse w hw)
      _ = F.card := by simp
      _ ≤ F.card + (goodJ n C s l 0).card := Nat.le_add_right _ _
  | succ k ih =>
    intro F hFlt hFfalse
    set w0 := n + n + k
    by_cases hw0 : w0 ∈ F
    · by_cases hle : (actSet n C l w0).card ≤ 1
      · set F' := F.erase w0
        have hFlt' : ∀ w ∈ F', w < n + n + k := fun w hw => by
          have hmem := Finset.mem_erase.mp hw
          have := hFlt w hmem.2
          omega
        have hFfalse' : ∀ w ∈ F', wireValue C (incidenceInput sᶜ {l}) w = false := fun w hw =>
          hFfalse w (Finset.mem_of_mem_erase hw)
        have hbu : F.biUnion (actSet n C l) ⊆ actSet n C l w0 ∪ F'.biUnion (actSet n C l) := by
          intro p hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨w, hw, hpw⟩ := hp
          by_cases hweq : w = w0
          · subst hweq; exact Finset.mem_union_left _ hpw
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hweq, hw⟩, hpw⟩)
        have hFcard : F'.card + 1 = F.card := Finset.card_erase_add_one hw0
        calc (F.biUnion (actSet n C l)).card
            ≤ (actSet n C l w0 ∪ F'.biUnion (actSet n C l)).card := Finset.card_le_card hbu
          _ ≤ (actSet n C l w0).card + (F'.biUnion (actSet n C l)).card := Finset.card_union_le _ _
          _ ≤ 1 + (F'.card + (goodJ n C s l k).card) :=
              Nat.add_le_add hle (ih F' hFlt' hFfalse')
          _ = F.card + (goodJ n C s l k).card := by omega
          _ ≤ F.card + (goodJ n C s l (k + 1)).card :=
              Nat.add_le_add_left (Finset.card_le_card (goodJ_mono C s l k)) _
      · have hge2 : 2 ≤ (actSet n C l w0).card := by omega
        have hk : k < C.size := by
          by_cases hlt : k < C.size
          · exact hlt
          · have hge : C.size ≤ k := Nat.le_of_not_lt hlt
            have hemp : actSet n C l w0 = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro p hp
              simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              rw [wires_ge C (incidenceInput {p} {l}) w0 (by rw [incidenceInput_length]; exact Nat.add_le_add_left hge _)] at hp
              cases hp
            rw [hemp] at hge2
            simp at hge2
        have hgat : gateAt C k = C.gates[k] := by
          simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        obtain ⟨hlen, hrb, heval_sc⟩ := step_gate_eval C hAO sᶜ l k hk
        set u0 := C.gates[k].inputs.getD 0 0
        set u1 := C.gates[k].inputs.getD 1 0
        have hu0_lt : u0 < n + n + k := hrb u0 (list_mem_getD_zero _ hlen 0)
        have hu1_lt : u1 < n + n + k := hrb u1 (list_mem_getD_one _ hlen 0)
        have hw0_false : wireValue C (incidenceInput sᶜ {l}) w0 = false := hFfalse w0 hw0
        rcases hAO.1 C.gates[k] (List.getElem_mem hk) with hop_and | hop_or
        · rw [hop_and] at heval_sc
          simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id] at heval_sc
          rw [hw0_false] at heval_sc
          have hdisj : wireValue C (incidenceInput sᶜ {l}) u0 = false ∨
              wireValue C (incidenceInput sᶜ {l}) u1 = false := by
            cases h0 : wireValue C (incidenceInput sᶜ {l}) u0
            · left; rfl
            · cases h1 : wireValue C (incidenceInput sᶜ {l}) u1
              · right; rfl
              · rw [h0, h1] at heval_sc; cases heval_sc
          have handle_branch : ∀ z : ℕ, z < n + n + k →
              wireValue C (incidenceInput sᶜ {l}) z = false →
              (∀ p : Fin n, wireValue C (incidenceInput {p} {l}) w0 = true →
                wireValue C (incidenceInput {p} {l}) z = true) →
              (F.biUnion (actSet n C l)).card ≤ F.card + (goodJ n C s l (k + 1)).card := by
            intro z hzlt hzfalse hzsub
            set F' := insert z (F.erase w0)
            have hFlt' : ∀ w ∈ F', w < n + n + k := fun w hw => by
              rcases Finset.mem_insert.mp hw with rfl | hw'
              · exact hzlt
              · have hmem := Finset.mem_erase.mp hw'
                have := hFlt w hmem.2
                omega
            have hFfalse' : ∀ w ∈ F', wireValue C (incidenceInput sᶜ {l}) w = false := fun w hw => by
              rcases Finset.mem_insert.mp hw with rfl | hw'
              · exact hzfalse
              · exact hFfalse w (Finset.mem_of_mem_erase hw')
            have hbu : F.biUnion (actSet n C l) ⊆ F'.biUnion (actSet n C l) := by
              intro p hp
              rw [Finset.mem_biUnion] at hp
              obtain ⟨w, hw, hpw⟩ := hp
              rw [Finset.mem_biUnion]
              by_cases hweq : w = w0
              · subst hweq
                refine ⟨z, Finset.mem_insert_self _ _, ?_⟩
                simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpw ⊢
                exact hzsub p hpw
              · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hw⟩), hpw⟩
            have hFcard : F'.card ≤ F.card := by
              have h1 : F'.card ≤ (F.erase w0).card + 1 := Finset.card_insert_le _ _
              have h2 : (F.erase w0).card + 1 = F.card := Finset.card_erase_add_one hw0
              omega
            calc (F.biUnion (actSet n C l)).card
                ≤ (F'.biUnion (actSet n C l)).card := Finset.card_le_card hbu
              _ ≤ F'.card + (goodJ n C s l k).card := ih F' hFlt' hFfalse'
              _ ≤ F.card + (goodJ n C s l k).card := Nat.add_le_add_right hFcard _
              _ ≤ F.card + (goodJ n C s l (k + 1)).card :=
                  Nat.add_le_add_left (Finset.card_le_card (goodJ_mono C s l k)) _
          rcases hdisj with hz0 | hz1
          · apply handle_branch u0 hu0_lt hz0
            intro p hp
            have heval_p := (step_gate_eval C hAO {p} l k hk).2.2
            rw [hop_and] at heval_p
            simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id] at heval_p
            rw [hp] at heval_p
            cases hpu0 : wireValue C (incidenceInput {p} {l}) u0
            · rw [hpu0] at heval_p; cases heval_p
            · rfl
          · apply handle_branch u1 hu1_lt hz1
            intro p hp
            have heval_p := (step_gate_eval C hAO {p} l k hk).2.2
            rw [hop_and] at heval_p
            simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id] at heval_p
            rw [hp] at heval_p
            cases hpu1 : wireValue C (incidenceInput {p} {l}) u1
            · rw [hpu1, Bool.and_false] at heval_p; cases heval_p
            · rfl
        · rw [hop_or] at heval_sc
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id] at heval_sc
          rw [hw0_false] at heval_sc
          have hu0_false : wireValue C (incidenceInput sᶜ {l}) u0 = false := by
            cases h0 : wireValue C (incidenceInput sᶜ {l}) u0
            · rfl
            · rw [h0] at heval_sc; cases heval_sc
          have hu1_false : wireValue C (incidenceInput sᶜ {l}) u1 = false := by
            cases h1 : wireValue C (incidenceInput sᶜ {l}) u1
            · rfl
            · rw [h1] at heval_sc
              cases h0 : wireValue C (incidenceInput sᶜ {l}) u0 <;> rw [h0] at heval_sc <;> cases heval_sc
          set F' := insert u0 (insert u1 (F.erase w0))
          have hFlt' : ∀ w ∈ F', w < n + n + k := fun w hw => by
            rcases Finset.mem_insert.mp hw with rfl | hw1
            · exact hu0_lt
            · rcases Finset.mem_insert.mp hw1 with rfl | hw2
              · exact hu1_lt
              · have hmem := Finset.mem_erase.mp hw2
                have := hFlt w hmem.2
                omega
          have hFfalse' : ∀ w ∈ F', wireValue C (incidenceInput sᶜ {l}) w = false := fun w hw => by
            rcases Finset.mem_insert.mp hw with rfl | hw1
            · exact hu0_false
            · rcases Finset.mem_insert.mp hw1 with rfl | hw2
              · exact hu1_false
              · exact hFfalse w (Finset.mem_of_mem_erase hw2)
          have hbu : F.biUnion (actSet n C l) ⊆ F'.biUnion (actSet n C l) := by
            intro p hp
            rw [Finset.mem_biUnion] at hp
            obtain ⟨w, hw, hpw⟩ := hp
            rw [Finset.mem_biUnion]
            by_cases hweq : w = w0
            · subst hweq
              simp only [actSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpw
              have heval_p := (step_gate_eval C hAO {p} l k hk).2.2
              rw [hop_or] at heval_p
              simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id] at heval_p
              rw [hpw] at heval_p
              by_cases hp0 : wireValue C (incidenceInput {p} {l}) u0 = true
              · refine ⟨u0, Finset.mem_insert_self _ _, ?_⟩
                simp [actSet, hp0]
              · have hp1 : wireValue C (incidenceInput {p} {l}) u1 = true := by
                  cases h0 : wireValue C (incidenceInput {p} {l}) u0
                  · cases h1 : wireValue C (incidenceInput {p} {l}) u1
                    · rw [h0, h1] at heval_p; cases heval_p
                    · rfl
                  · exact absurd h0 hp0
                refine ⟨u1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
                simp [actSet, hp1]
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hw⟩)), hpw⟩
          have hFcard : F'.card ≤ F.card + 1 := by
            have h1 : F'.card ≤ (insert u1 (F.erase w0)).card + 1 := Finset.card_insert_le _ _
            have h2 : (insert u1 (F.erase w0)).card ≤ (F.erase w0).card + 1 := Finset.card_insert_le _ _
            have h3 : (F.erase w0).card + 1 = F.card := Finset.card_erase_add_one hw0
            omega
          have hJstep : (goodJ n C s l (k + 1)).card = (goodJ n C s l k).card + 1 :=
            goodJ_step C s l k hk (by rw [hgat, hop_or]) hw0_false hge2
          calc (F.biUnion (actSet n C l)).card
              ≤ (F'.biUnion (actSet n C l)).card := Finset.card_le_card hbu
            _ ≤ F'.card + (goodJ n C s l k).card := ih F' hFlt' hFfalse'
            _ ≤ F.card + 1 + (goodJ n C s l k).card := Nat.add_le_add_right hFcard _
            _ = F.card + (goodJ n C s l (k + 1)).card := by omega
    · have hFlt' : ∀ w ∈ F, w < n + n + k := fun w hw' => by
        have := hFlt w hw'
        have hne : w ≠ w0 := fun heq => hw0 (heq ▸ hw')
        omega
      calc (F.biUnion (actSet n C l)).card
          ≤ F.card + (goodJ n C s l k).card := ih F hFlt' hFfalse
        _ ≤ F.card + (goodJ n C s l (k + 1)).card :=
            Nat.add_le_add_left (Finset.card_le_card (goodJ_mono C s l k)) _

end PEqualNP.Outside.L_meta_3256

theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C s l hAO hOut hPos hNeg
  refine ⟨PEqualNP.Outside.L_meta_3256.goodJ n C s l C.size, ?_, ?_⟩
  · have hbound := PEqualNP.Outside.L_meta_3256.biUnion_actSet_bound C hAO s l C.size {C.output}
      (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hOut)
      (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hNeg)
    have hsub : s ⊆ ({C.output} : Finset ℕ).biUnion (PEqualNP.Outside.L_meta_3256.actSet n C l) := by
      intro p hp
      rw [Finset.mem_biUnion]
      refine ⟨C.output, Finset.mem_singleton_self _, ?_⟩
      simp only [PEqualNP.Outside.L_meta_3256.actSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hPos p hp
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hbound
    omega
  · intro j hj
    simp only [PEqualNP.Outside.L_meta_3256.goodJ, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨_, hjlt, hjop, hjfalse, hjcard⟩ := hj
    rw [PEqualNP.Outside.L_meta_3256.isOr_iff] at hjop
    refine ⟨hjlt, hjop, hjfalse, ?_, ?_⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (PEqualNP.Outside.L_meta_3256.actSet n C l (n + n + j)).card)
      simp only [PEqualNP.Outside.L_meta_3256.actSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact ⟨a, b, hab, ha, hb⟩
    · intro p hp
      by_contra hpns
      have hsub : ({p} : Finset (Fin n)) ⊆ sᶜ := Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hpns)
      have htrue := PEqualNP.Outside.L_meta_3256.wireValue_mono C hAO.1 l {p} sᶜ hsub (n + n + j) hp
      rw [htrue] at hjfalse
      cases hjfalse
