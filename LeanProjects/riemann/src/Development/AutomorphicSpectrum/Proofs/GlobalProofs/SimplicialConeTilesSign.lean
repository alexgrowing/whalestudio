import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComboNotMemSpan

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem signConst_of_nonneg (l : V →ₗ[ℚ] ℚ) (s : Finset V) (h : ∀ v ∈ s, 0 ≤ l v) : SignConst l (coneOn s) := by
  unfold SignConst
  by_cases hz : ∀ v ∈ s, l v = 0
  · refine Or.inl ?_
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, -, rfl⟩ := hx
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => by rw [map_smul, hz i hi, smul_zero])
  · refine Or.inr (Or.inl ?_)
    push_neg at hz
    obtain ⟨w, hw, hlw⟩ := hz
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [map_sum]
    have hnn : ∀ i ∈ s, 0 ≤ l (t i • i) := fun i hi => by
      rw [map_smul, smul_eq_mul]; exact mul_nonneg (ht i hi).le (h i hi)
    have hpos : 0 < l (t w • w) := by
      rw [map_smul, smul_eq_mul]; exact mul_pos (ht w hw) (lt_of_le_of_ne (h w hw) (Ne.symm hlw))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnn hw)

theorem signConst_of_nonpos (l : V →ₗ[ℚ] ℚ) (s : Finset V) (h : ∀ v ∈ s, l v ≤ 0) : SignConst l (coneOn s) := by
  unfold SignConst
  by_cases hz : ∀ v ∈ s, l v = 0
  · refine Or.inl ?_
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, -, rfl⟩ := hx
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => by rw [map_smul, hz i hi, smul_zero])
  · refine Or.inr (Or.inr ?_)
    push_neg at hz
    obtain ⟨w, hw, hlw⟩ := hz
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [map_sum]
    have hnp : ∀ i ∈ s, 0 ≤ -l (t i • i) := fun i hi => by
      rw [map_smul, smul_eq_mul]; nlinarith [(ht i hi).le, h i hi]
    have hneg : l (t w • w) < 0 := by
      have hlt : l w < 0 := lt_of_le_of_ne (h w hw) hlw
      rw [map_smul, smul_eq_mul]; nlinarith [ht w hw]
    have key := Finset.single_le_sum hnp hw
    simp only [Finset.sum_neg_distrib] at key
    linarith

private theorem sum_insert_insert_ite_ite_smul [DecidableEq V] {p q : V} {X : Finset V} (hp : p ∉ insert q X) (hq : q ∉ X)
    (α β : ℚ) (t : V → ℚ) :
    ∑ i ∈ insert p (insert q X), (if i = p then α else if i = q then β else t i) • i
      = α • p + (β • q + ∑ i ∈ X, t i • i) := by
  have hqp : q ≠ p := fun e => hp (by rw [← e]; exact Finset.mem_insert_self q X)
  have hpX : p ∉ X := fun e => hp (Finset.mem_insert_of_mem e)
  have hX : ∑ i ∈ X, (if i = p then α else if i = q then β else t i) • i = ∑ i ∈ X, t i • i :=
    Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (fun e => hpX (by rw [← e]; exact hj)), if_neg (fun e => hq (by rw [← e]; exact hj))])
  rw [Finset.sum_insert hp, Finset.sum_insert hq, if_pos rfl, if_neg hqp, if_pos rfl, hX]

private theorem sum_insert_ite_smul [DecidableEq V] {p : V} {X : Finset V} (hp : p ∉ X) (α : ℚ) (t : V → ℚ) :
    ∑ i ∈ insert p X, (if i = p then α else t i) • i = α • p + ∑ i ∈ X, t i • i := by
  have hX : ∑ i ∈ X, (if i = p then α else t i) • i = ∑ i ∈ X, t i • i :=
    Finset.sum_congr rfl (fun j hj => by rw [if_neg (fun e => hp (by rw [← e]; exact hj))])
  rw [Finset.sum_insert hp, if_pos rfl, hX]

private theorem pos_ite_ite_of_pos_insert_insert [DecidableEq V] {p q : V} {X : Finset V} {α β : ℚ} {t : V → ℚ}
    (hα : 0 < α) (hβ : 0 < β) (ht : ∀ j ∈ X, 0 < t j) :
    ∀ i ∈ insert p (insert q X), 0 < (if i = p then α else if i = q then β else t i) := by
  intro i hi
  split_ifs with h1 h2
  · exact hα
  · exact hβ
  · exact ht i ((Finset.mem_insert.mp ((Finset.mem_insert.mp hi).resolve_left h1)).resolve_left h2)

private theorem pos_ite_of_pos_insert [DecidableEq V] {p : V} {X : Finset V} {α : ℚ} {t : V → ℚ}
    (hα : 0 < α) (ht : ∀ j ∈ X, 0 < t j) :
    ∀ i ∈ insert p X, 0 < (if i = p then α else t i) := by
  intro i hi
  split_ifs with h1
  · exact hα
  · exact ht i ((Finset.mem_insert.mp hi).resolve_left h1)

private theorem eq_of_sum_smul_eq_of_linearIndepOn {s : Finset V} (hs : LinearIndepOn ℚ id (s : Set V)) (T T' : V → ℚ)
    (h : ∑ i ∈ s, T i • i = ∑ i ∈ s, T' i • i) : ∀ i ∈ s, T i = T' i := by
  have h0 : ∑ i ∈ s, (T i - T' i) • id i = 0 := by
    simp only [id, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  intro i hi
  exact sub_eq_zero.mp (linearIndepOn_finset_iff.mp hs (fun i => T i - T' i) h0 i hi)

private theorem coeff_eq_of_linearIndepOn_insert_insert [DecidableEq V] {p q : V} {X : Finset V} (hp : p ∉ insert q X) (hq : q ∉ X)
    (hli : LinearIndepOn ℚ id ((insert p (insert q X) : Finset V) : Set V)) {α β α' β' : ℚ} {t t' : V → ℚ}
    (h : α • p + (β • q + ∑ i ∈ X, t i • i) = α' • p + (β' • q + ∑ i ∈ X, t' i • i)) :
    α = α' ∧ β = β' := by
  have hqp : q ≠ p := fun e => hp (by rw [← e]; exact Finset.mem_insert_self q X)
  rw [← sum_insert_insert_ite_ite_smul hp hq α β t, ← sum_insert_insert_ite_ite_smul hp hq α' β' t'] at h
  have hc := eq_of_sum_smul_eq_of_linearIndepOn hli _ _ h
  have h1 := hc p (Finset.mem_insert_self _ _)
  have h2 := hc q (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  exact ⟨by simpa using h1, by simpa [hqp] using h2⟩

private theorem exists_coords_lt_of_mem_coneOn_insert_u_c [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hu : u ∉ insert c r) (hcr : c ∉ r) {x : V}
    (hx : x ∈ coneOn (insert u (insert c r))) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ β * a < α * b := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htu : 0 < t u := ht u (Finset.mem_insert_self _ _)
  have htc : 0 < t c := ht c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨t u + t c * a, t c * b, t, add_pos htu (mul_pos htc ha), mul_pos htc hb,
    fun j hj => ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)), ?_,
    by nlinarith [mul_pos htu hb]⟩
  rw [Finset.sum_insert hu, Finset.sum_insert hcr, hc]
  module

private theorem exists_coords_lt_swap_of_mem_coneOn_c_w [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hcw : c ∉ insert w r) (hwr : w ∉ r) {x : V}
    (hx : x ∈ coneOn (insert c (insert w r))) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ α * b < β * a := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htc : 0 < t c := ht c (Finset.mem_insert_self _ _)
  have htw : 0 < t w := ht w (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨t c * a, t c * b + t w, t, mul_pos htc ha, add_pos (mul_pos htc hb) htw,
    fun j hj => ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)), ?_,
    by nlinarith [mul_pos htw ha]⟩
  rw [Finset.sum_insert hcw, Finset.sum_insert hwr, hc]
  module

private theorem exists_coords_eq_of_mem_coneOn_insert_c [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hcr : c ∉ r) {x : V} (hx : x ∈ coneOn (insert c r)) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ α * b = β * a := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htc : 0 < t c := ht c (Finset.mem_insert_self _ _)
  refine ⟨t c * a, t c * b, t, mul_pos htc ha, mul_pos htc hb,
    fun j hj => ht j (Finset.mem_insert_of_mem hj), ?_, by ring⟩
  rw [Finset.sum_insert hcr, hc]
  module

private theorem coneOn_u_w_subset_union [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (huw : u ∉ insert w r) (hwr : w ∉ r) (huc : u ∉ insert c r)
    (hcr : c ∉ r) (hcw : c ∉ insert w r) {x : V} (hx : x ∈ coneOn (insert u (insert w r))) :
    x ∈ coneOn (insert u (insert c r)) ∪ coneOn (insert c (insert w r)) ∪ coneOn (insert c r) := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htu : 0 < t u := ht u (Finset.mem_insert_self _ _)
  have htw : 0 < t w := ht w (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have htr : ∀ j ∈ r, 0 < t j := fun j hj =>
    ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj))
  rw [Finset.sum_insert huw, Finset.sum_insert hwr]
  rcases lt_trichotomy (t w * a) (t u * b) with h | h | h
  · refine Or.inl (Or.inl ?_)
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * b = t w := ⟨t w / b, div_mul_cancel₀ _ hb.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have e : (t u - k * a) * b = t u * b - t w * a := by rw [← hk]; ring
    have hm : 0 < (t u - k * a) * b := by rw [e]; linarith
    have hku : 0 < t u - k * a := by nlinarith
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = u then t u - k * a else if i = c then k else t i,
      pos_ite_ite_of_pos_insert_insert hku hk0 htr, ?_⟩
    beta_reduce
    rw [sum_insert_insert_ite_ite_smul huc hcr, hc, ← hk]
    module
  · refine Or.inr ?_
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * a = t u := ⟨t u / a, div_mul_cancel₀ _ ha.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have hkb : k * b = t w := mul_right_cancel₀ ha.ne' (by rw [h, ← hk]; ring)
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = c then k else t i, pos_ite_of_pos_insert hk0 htr, ?_⟩
    beta_reduce
    rw [sum_insert_ite_smul hcr, hc, ← hk, ← hkb]
    module
  · refine Or.inl (Or.inr ?_)
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * a = t u := ⟨t u / a, div_mul_cancel₀ _ ha.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have e : (t w - k * b) * a = t w * a - t u * b := by rw [← hk]; ring
    have hm : 0 < (t w - k * b) * a := by rw [e]; linarith
    have hkw : 0 < t w - k * b := by nlinarith
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = c then k else if i = w then t w - k * b else t i,
      pos_ite_ite_of_pos_insert_insert hk0 hkw htr, ?_⟩
    beta_reduce
    rw [sum_insert_insert_ite_ite_smul hcw hwr, hc, ← hk]
    module

theorem tile_of_card_lt [DecidableEq V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (n : ℕ) :
    ∀ s : Finset V, (s.filter (fun v => l v ≠ 0)).card < n → LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
      Tile (P : Set V) (SignConst l) (coneOn s) := by
  have hfr : ∀ (x : V) (X : Finset V), l x = 0 →
      ((insert x X).filter (fun v => l v ≠ 0)).card = (X.filter (fun v => l v ≠ 0)).card := by
    intro x X hx
    rw [Finset.filter_insert, if_neg (not_not.mpr hx)]
  have hfi : ∀ (x : V) (X : Finset V), l x ≠ 0 → x ∉ X →
      ((insert x X).filter (fun v => l v ≠ 0)).card = (X.filter (fun v => l v ≠ 0)).card + 1 := by
    intro x X hx hxX
    rw [Finset.filter_insert, if_pos hx, Finset.card_insert_eq_ite,
      if_neg (fun h => hxX (Finset.mem_filter.mp h).1)]
  induction n with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
    intro s hs hli hP
    by_cases hnn : ∀ v ∈ s, 0 ≤ l v
    · exact Tile.cone s hli hP (signConst_of_nonneg l s hnn)
    by_cases hnp : ∀ v ∈ s, l v ≤ 0
    · exact Tile.cone s hli hP (signConst_of_nonpos l s hnp)
    push_neg at hnn hnp
    obtain ⟨w, hws, hlw⟩ := hnn
    obtain ⟨u, hus, hlu⟩ := hnp
    have huw : u ≠ w := by rintro rfl; linarith
    obtain ⟨r, hur, hwr, rfl⟩ : ∃ r : Finset V, u ∉ r ∧ w ∉ r ∧ s = insert u (insert w r) :=
      ⟨(s.erase u).erase w, by simp, by simp,
        by rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨huw.symm, hws⟩), Finset.insert_erase hus]⟩
    have huwr : u ∉ insert w r := by simp [huw, hur]
    have hlw0 : l w ≠ 0 := hlw.ne
    have hlu0 : l u ≠ 0 := hlu.ne'
    have ha : (0 : ℚ) < -l w := by linarith
    have hb : (0 : ℚ) < l u := hlu
    have hPu : u ∈ P := hP (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
    have hPw : w ∈ P := hP (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have hPr : ∀ x ∈ r, x ∈ P := fun x hx =>
      hP (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
    have hcP : (-l w) • u + (l u) • w ∈ P := P.add_mem (P.smul_mem ha hPu) (P.smul_mem hb hPw)
    have hlc : l ((-l w) • u + (l u) • w) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    obtain ⟨hcr, hcu, hcw, hli1, hli2, hli3⟩ := StellarLI.main u w r (-l w) (l u) ha hb huw hur hwr hli
    generalize hcdef : (-l w) • u + (l u) • w = c at hcP hlc hcr hcu hcw hli1 hli2 hli3
    have hc' : c = (-l w) • u + (l u) • w := hcdef.symm
    have huc : u ∉ insert c r := by simp [Ne.symm hcu, hur]
    have hcwr : c ∉ insert w r := by simp [hcw, hcr]
    have hs' := hs
    rw [hfi u _ hlu0 huwr, hfi w r hlw0 hwr] at hs'
    have hcA : ((insert u (insert c r)).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfi u _ hlu0 huc, hfr c r hlc]; omega
    have hcB : ((insert c (insert w r)).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfr c _ hlc, hfi w r hlw0 hwr]; omega
    have hcC : ((insert c r).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfr c r hlc]; omega
    have hsubA : ((insert u (insert c r) : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h | h
      · rw [h]; exact hPu
      · rw [h]; exact hcP
      · exact hPr x h
    have hsubB : ((insert c (insert w r) : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h | h
      · rw [h]; exact hcP
      · rw [h]; exact hPw
      · exact hPr x h
    have hsubC : ((insert c r : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h
      · rw [h]; exact hcP
      · exact hPr x h
    have hA := ih _ hcA hli2 hsubA
    have hB := ih _ hcB hli1 hsubB
    have hC := ih _ hcC hli3 hsubC
    have dAB : Disjoint (coneOn (insert u (insert c r))) (coneOn (insert c (insert w r))) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dAC : Disjoint (coneOn (insert u (insert c r))) (coneOn (insert c r)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dBC : Disjoint (coneOn (insert c (insert w r))) (coneOn (insert c r)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dABC : Disjoint (coneOn (insert u (insert c r)) ∪ coneOn (insert c (insert w r)))
        (coneOn (insert c r)) := Set.disjoint_union_left.mpr ⟨dAC, dBC⟩
    have heq : coneOn (insert u (insert w r)) = (coneOn (insert u (insert c r)) ∪
        coneOn (insert c (insert w r))) ∪ coneOn (insert c r) := by
      ext x
      constructor
      · exact fun hx => coneOn_u_w_subset_union hc' ha hb huwr hwr huc hcr hcwr hx
      · intro hx
        have key : ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
            x = α • u + (β • w + ∑ j ∈ r, t j • j) := by
          rcases hx with (hx | hx) | hx
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
        obtain ⟨α, β, t, h1, h2, h3, h4⟩ := key
        simp only [coneOn, Set.mem_setOf_eq]
        refine ⟨fun i => if i = u then α else if i = w then β else t i, pos_ite_ite_of_pos_insert_insert h1 h2 h3, ?_⟩
        beta_reduce
        rw [sum_insert_insert_ite_ite_smul huwr hwr]
        exact h4
    rw [heq]
    exact Tile.union (Tile.union hA hB dAB) hC dABC

theorem main : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (s : Finset V), LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
    Tile (P : Set V) (SignConst l) (coneOn s) := by
  intro V _ _ P l s hli hP
  classical
  exact tile_of_card_lt P l _ s (Nat.lt_succ_self _) hli hP

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign
