import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecomp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel

noncomputable section

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a c : ℕ) (x : Gn p (a + 1 + c)) :
    StdBlock a x ↔ InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ br (a + 1) c (x : Mt p (a + 1 + c)) = 1 ∧
      ∀ i j : Fin (a + 1), (j : ℕ) < a → tl (a + 1) (x : Mt p (a + 1 + c)) i j = if i = j then 1 else 0 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, fun i j hj => ?_⟩
    · rw [h i j (by omega), if_neg]
      intro e; subst e; omega
    · ext i j
      simp only [br, entN]
      rw [dif_pos (by omega), h _ _ (by simp; omega)]
      simp [Matrix.one_apply, Fin.ext_iff]
    · simp only [tl, entN]
      rw [dif_pos (by omega), h _ _ (by simp; omega)]
      simp [Fin.ext_iff]
  · rintro ⟨h1, h2, h3⟩ i j hij
    by_cases hi : (i : ℕ) ≤ a
    · have hj : (j : ℕ) < a := by omega
      have := h3 ⟨i, by omega⟩ ⟨j, by omega⟩ hj
      simp only [tl, entN] at this
      rw [dif_pos (by omega)] at this
      simpa [Fin.ext_iff] using this
    · by_cases hj : (j : ℕ) < a + 1
      · rw [h1 i j hj (by omega), if_neg]
        intro e; subst e; omega
      · have := congrFun (congrFun h2 ⟨(i : ℕ) - (a + 1), by omega⟩) ⟨(j : ℕ) - (a + 1), by omega⟩
        simp only [br, entN] at this
        rw [dif_pos (by omega)] at this
        have ei : (⟨a + 1 + ((i : ℕ) - (a + 1)), by omega⟩ : Fin (a + 1 + c)) = i := Fin.ext (by simp; omega)
        have ej : (⟨a + 1 + ((j : ℕ) - (a + 1)), by omega⟩ : Fin (a + 1 + c)) = j := Fin.ext (by simp; omega)
        rw [ei, ej, Matrix.one_apply] at this
        rw [this]
        simp only [Fin.ext_iff]
        congr 1
        apply propext
        omega

theorem isUnit_tl (a c : ℕ) (x : Gn p (a + 1 + c)) (h1 : InPar (a + 1) (x : Mt p (a + 1 + c)))
    (h2 : br (a + 1) c (x : Mt p (a + 1 + c)) = 1) : IsUnit (tl (a + 1) (x : Mt p (a + 1 + c))) := by
  have := LabelDet.det_inPar (a + 1) c (x : Mt p (a + 1 + c)) h1
  rw [h2, Matrix.det_one, mul_one] at this
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (this ▸ x.det_ne_zero))

theorem val_toG {n : ℕ} (M : Mt p n) (h : IsUnit M) : ((toG M : Gn p n) : Mt p n) = M := by
  unfold toG
  rw [dif_pos h]
  rfl

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdTrace_eq (a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : Gn p (a + 1 + c) → ℂ) :
    stdTrace a θ ψ = (p : ℂ) ^ ((a + 1) * c) * ∑ y : Gn p (a + 1),
      if StdBlock a y then (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0 := by
  have hp0 : (p : ℂ) ^ ((a + 1) * c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : (p : ℂ) ^ ((a + 1) * c) * (∑ y : Gn p (a + 1),
      if StdBlock a y then (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0) =
      ∑ y : Gn p (a + 1), ∑ x : Gn p (a + 1 + c),
        if StdBlock a y ∧ (InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ tl (a + 1) (x : Mt p (a + 1 + c)) = (y : Mt p (a + 1)) ∧
          br (a + 1) c (x : Mt p (a + 1 + c)) = ((1 : Gn p c) : Mt p c)) then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * ψ x else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold res
    by_cases hy : StdBlock a y
    · rw [if_pos hy, mul_left_comm, mul_inv_cancel_left₀ hp0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hy, true_and, mul_ite, mul_zero]
    · simp [hy]
  rw [e1, Finset.sum_comm]
  unfold stdTrace
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ br (a + 1) c (x : Mt p (a + 1 + c)) = 1
  · have hu := isUnit_tl a c x hx.1 hx.2
    have hy0 := val_toG _ hu
    rw [Finset.sum_eq_single (toG (tl (a + 1) (x : Mt p (a + 1 + c))))]
    · have hs : StdBlock a x ↔ StdBlock a (toG (tl (a + 1) (x : Mt p (a + 1 + c)))) := by
        rw [stdBlock_iff]
        unfold StdBlock
        rw [hy0]
        constructor
        · rintro ⟨-, -, h⟩ i j hij
          exact h i j (by have := i.isLt; omega)
        · intro h
          exact ⟨hx.1, hx.2, fun i j hj => h i j (by omega)⟩
      have hd : Matrix.GeneralLinearGroup.det x =
          Matrix.GeneralLinearGroup.det (toG (tl (a + 1) (x : Mt p (a + 1 + c)))) := by
        rw [LabelDet.det_par (a + 1) c x hx.1, hx.2, LabelDet.toG_one, map_one, mul_one]
      by_cases h : StdBlock a x
      · rw [if_pos h, if_pos ⟨hs.1 h, hx.1, hy0.symm, by simpa using hx.2⟩, hd]
      · rw [if_neg h, if_neg (fun e => h (hs.2 e.1))]
    · intro y _ hne
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hne (Units.ext (h.symm.trans hy0.symm))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hx ⟨((stdBlock_iff a c x).1 h).1, ((stdBlock_iff a c x).1 h).2.1⟩), eq_comm]
    refine Finset.sum_eq_zero fun y _ => if_neg ?_
    rintro ⟨-, h1, -, h3⟩
    exact hx ⟨h1, by simpa using h3⟩

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem sum_list_comm {ι X : Type} [Fintype ι] (L : List X) (f : ι → X → ℂ) :
    ∑ i, (L.map (f i)).sum = (L.map fun q => ∑ i, f i q).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [Finset.sum_add_distrib, ih]

theorem list_sum_nat (l : List ℂ) (h : ∀ z ∈ l, ∃ n : ℕ, z = n) :
    (∃ n : ℕ, l.sum = n) ∧ ∀ z ∈ l, z ≠ 0 → ∃ n : ℕ, l.sum = n + 1 := by
  induction l with
  | nil => exact ⟨⟨0, by simp⟩, by simp⟩
  | cons z l ih =>
    obtain ⟨⟨k, hk⟩, H⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨m, hm⟩ := h z List.mem_cons_self
    refine ⟨⟨m + k, by rw [List.sum_cons, hk, hm]; push_cast; ring⟩, fun w hw hw0 => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
        have : m ≠ 0 := by rintro rfl; exact hw0 (by simpa using hm)
        omega⟩
      exact ⟨m' + k, by rw [List.sum_cons, hk, hm]; push_cast; ring⟩
    · obtain ⟨k', hk'⟩ := H w hw hw0
      exact ⟨m + k', by rw [List.sum_cons, hk', hm]; push_cast; ring⟩

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_nat {G : Type} [Group G] [Fintype G] {α β : G → ℂ} (hα : IsChar α) (hβ : IsChar β) :
    ∃ n : ℕ, ip α β = n := by
  obtain ⟨W, hW⟩ := hα
  obtain ⟨V, hV⟩ := hβ
  refine ⟨Module.finrank ℂ (V ⟶ W), ?_⟩
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant]
  unfold ip
  rw [Fintype.card_eq_nat_card]
  simp [hW, hV]

theorem ip_self {G : Type} [Group G] [Fintype G] {α : G → ℂ} (hα : IsIrr α) : ip α α = 1 := by
  obtain ⟨V, hs, hV⟩ := hα
  haveI := hs
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have := FDRep.char_orthonormal V V
  rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at this
  unfold ip
  rw [Fintype.card_eq_nat_card]
  simpa [hV] using this

theorem isChar_of_isIrr {G : Type} [Group G] {α : G → ℂ} (h : IsIrr α) : IsChar α := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.LevelType

open GlobalTheory.GLq GlobalTheory.GLq.StdRes Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (ψ : GlobalTheory.GLq.Gn p r → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsChar ψ → stdTrace a θ ψ ≠ 0 →
    ∃ (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ), GlobalTheory.GLq.IsIrr α ∧ GlobalTheory.GLq.IsIrr β ∧
      GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 ∧ stdTrace a θ α ≠ 0 := by
  intro p _ r a c θ ψ hr hψ hne
  subst hr
  obtain ⟨L, hLirr, hL⟩ := (HCChar.hc_isChar_and_res_decomp p (a + 1) c (a + 1 + c) rfl).2 ψ hψ
  obtain ⟨q, hq, hqt⟩ : ∃ q ∈ L, stdTrace a θ q.1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [stdTrace_eq]
    have e1 : (∑ y : Gn p (a + 1), if StdBlock a y then
        (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0) =
        ∑ y : Gn p (a + 1), (L.map fun q => if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * (q.1 y * q.2 1) else 0).sum := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hL]
      by_cases hy : StdBlock a y
      · simp only [hy, if_true]
        rw [List.sum_map_mul_left]
      · simp [hy]
    rw [e1, sum_list_comm, List.sum_eq_zero, mul_zero]
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
    have := hcon q hq
    unfold stdTrace at this
    calc (∑ y : Gn p (a + 1), if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * (q.1 y * q.2 1) else 0)
        = (∑ y : Gn p (a + 1), if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * q.1 y else 0) * q.2 1 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs
          · ring
          · simp
      _ = 0 := by rw [this, zero_mul]
  refine ⟨q.1, q.2, (hLirr q hq).1, (hLirr q hq).2, ?_, hqt⟩
  rw [hc, FrobRecHC.hcT_adjoint p (a + 1) c (a + 1 + c) rfl ψ _ (isClass_of_isChar hψ)]
  have e : ip (fun pr : Gn p (a + 1) × Gn p c => res (a + 1) c ψ pr.1 pr.2) (fun pr => q.1 pr.1 * q.2 pr.2) =
      (L.map fun q' => ip q'.1 q.1 * ip q'.2 q.2).sum := by
    unfold ip
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
    simp only [hL, Prod.fst_inv, Prod.snd_inv]
    have hs : ∀ (x : Gn p (a + 1)) (y : Gn p c), (L.map fun q' => q'.1 x * q'.2 y).sum * (q.1 x⁻¹ * q.2 y⁻¹) =
        (L.map fun q' => q'.1 x * q'.2 y * (q.1 x⁻¹ * q.2 y⁻¹)).sum := fun x y => by rw [List.sum_map_mul_right]
    simp only [hs]
    rw [Finset.sum_congr rfl fun x _ => sum_list_comm L fun y q' => q'.1 x * q'.2 y * (q.1 x⁻¹ * q.2 y⁻¹),
      sum_list_comm, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q' _
    rw [mul_inv, mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  have hnat : ∀ z ∈ L.map (fun q' => ip q'.1 q.1 * ip q'.2 q.2), ∃ n : ℕ, z = n := by
    intro z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hz
    obtain ⟨m, hm⟩ := ip_nat (isChar_of_isIrr (hLirr q' hq').1) (isChar_of_isIrr (hLirr q hq).1)
    obtain ⟨k, hk⟩ := ip_nat (isChar_of_isIrr (hLirr q' hq').2) (isChar_of_isIrr (hLirr q hq).2)
    exact ⟨m * k, by rw [hm, hk]; push_cast; ring⟩
  obtain ⟨n, hn⟩ := (list_sum_nat _ hnat).2 _ (List.mem_map_of_mem hq)
    (by show ip q.1 q.1 * ip q.2 q.2 ≠ 0; rw [ip_self (hLirr q hq).1, ip_self (hLirr q hq).2]; norm_num)
  rw [hn]
  exact_mod_cast Nat.succ_ne_zero n

end GlobalTheory.LevelType
