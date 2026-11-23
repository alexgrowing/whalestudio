import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormPowMulProdTranslConst
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHarmonicAndMemMinorSpan

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem hasSum_prod_of_fintype {J ι : Type*} [Fintype J] {f : J → ι → ℂ} {y : J → ℂ}
    (hf : ∀ j, Summable fun m => ‖f j m‖) (h : ∀ j, HasSum (f j) (y j)) :
    (Summable fun p : J × ι => ‖f p.1 p.2‖) ∧ HasSum (fun p : J × ι => f p.1 p.2) (∑ j, y j) := by
  have h1 : Summable fun p : J × ι => ‖f p.1 p.2‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hf, Summable.of_finite⟩
  have h2 := h1.of_norm.hasSum
  exact ⟨h1, (h2.prod_fiberwise h).unique (hasSum_fintype y) ▸ h2⟩

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  have hm : P ∈ GaussGauge.minorSpan (Fin n) c c' :=
    GaussGauge.orbitSpan_le_minorSpan (add_comm X.p0 q0 ▸ hpq) c c'
      (Harm.rowHighest_eq_orbitSpan (add_comm X.p0 q0 ▸ hpq) c c' ℂ ▸ hP)
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) hm hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

variable {J : Type*} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
  {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ}

theorem isSec_of_eq_sum_thFr (hs : IsSympl X bas) (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    X.IsSec (wtOf X hr c c' n) Q := by
  refine ⟨DifferentiableOn.congr (DifferentiableOn.fun_sum fun j hj => ?_) hQ,
    fun x hx u hu => ?_, hΓ⟩
  · exact (differentiableOn_thFr idx hs hr n _ _
      (Harm.isHarmonic_of_mem_rowHighest (hP j hj))).const_mul _
  · rw [hQ _ (PerMove.rmul_mem_GG hx hu), hQ x hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [thFr_rmul idx hr _ _ hs (hP j hj) hx hu, mul_left_comm]

theorem isModerate_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x) :
    X.IsModerate (wtOf X hr c c' n) Q := by
  obtain ⟨C, A, h⟩ := isModerate_sum_thFr idx hr hs hn s t a b hP
  exact ⟨C, A, fun x hx => by simpa only [Data.pnorm, hQ x hx] using h x hx⟩

theorem exists_expansion_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ (A : s × (Fin n → Fin g → ℤ) → ℂ) (ν : s × (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ u : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * u τ))
        (Q (X.flow ξ (fun τ => (u τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hpq hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine ⟨fun p => t p.1 * A p.1 p.2, fun p => ν p.1 p.2,
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1, fun u => ?_,
    fun p hp => h3 _ _ (right_ne_zero_of_mul hp)⟩
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

theorem mem_SS_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hc : (X.p0 + q0 ≤ n ∧ ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i) ∨ ∀ ξ, ¬ X.IsIso ξ)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  obtain ⟨hpq, hc⟩ := hc.resolve_right fun h => h ξ hξ
  obtain ⟨A, ν, h1, h2, h3⟩ := exists_expansion_of_eq_sum_thFr idx hr s t a b hs hn hpq hc hP hQ hξ hx
  exact FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx A h1 ν h2 0 h3

example : ∃ (c : HyperbolicCusp.flagData.Ψ → Fin 1 → ℕ)
    (c' : HyperbolicCusp.flagData.Ψ → Fin HyperbolicCusp.flagData.p0 → ℕ)
    (P : Harm.Poly ℂ HyperbolicCusp.flagData.Ψ 1 HyperbolicCusp.flagData.p0 (Fin 2)),
    IsSympl _ Gauss.bas ∧ HyperbolicCusp.flagData.IsIso ![1, 1] ∧
      HyperbolicCusp.flagData.p0 + 1 ≤ 2 ∧ (∃ τ, ∃ i : Fin 1, i.val + 1 = 1 ∧ 1 ≤ c τ i) ∧
      P ∈ Harm.rowHighest ℂ c c' ∧ P ≠ 0 := by
  have h : 1 + HyperbolicCusp.flagData.p0 ≤ 2 := (add_comm _ _).trans_le Gauss.hr.le
  obtain ⟨τ⟩ := nonempty_type HyperbolicCusp.flagData
  refine ⟨fun _ _ => 1, fun _ _ => 0, Harm.basePoly ℂ h (fun _ _ => 1) fun _ _ => 0,
    Gauss.isSympl_bas,
    HyperbolicCusp.isIso_one, Gauss.hr.le, ⟨τ, 0, rfl, le_rfl⟩, ?_, Harm.basePoly_ne_zero h _ _⟩
  exact Harm.basePoly_mem_rowHighest h _ _

end

end GlobalTheory.ThFr
