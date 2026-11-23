import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFundamentalDomainCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodQuadraticFormsSmooth
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.QuasiPeriodicExp

theorem continuous_per {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : Continuous (per A) := by
  unfold per vecMul dotProduct
  fun_prop

theorem quot_const {g : ℕ} {A : Matrix (Fin g) (Fin g) ℂ} (hA : (A.map Complex.im).det ≠ 0)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0)
    (hper : ∀ l ∈ stdLat g, ∃ c : ℂ, ∀ z, f (z + per A l) = c * f z) (w z : Fin g → ℂ) :
    f (z + w) / f z = f w / f 0 := by
  set h : (Fin g → ℂ) → ℂ := fun z => f (z + w) / f z with hh
  have hd : Differentiable ℂ h := by
    have e : h = fun x => f (x + w) * (f x)⁻¹ := by
      funext x; simp [hh, div_eq_mul_inv]
    rw [e]
    exact (hf.comp (differentiable_id.add_const w)).mul (hf.inv hf0)
  have hpe : ∀ l ∈ stdLat g, ∀ z, h (z + per A l) = h z := by
    intro l hl z
    obtain ⟨c, hc⟩ := hper l hl
    have hc0 : c ≠ 0 := by
      intro h0
      have := hc z
      rw [h0, zero_mul] at this
      exact hf0 _ this
    simp only [hh]
    rw [show z + per A l + w = (z + w) + per A l by abel, hc, hc, mul_div_mul_left _ _ hc0]
  have hb : Bornology.IsBounded (Set.range h) := by
    have hK : IsCompact (h '' (per A '' Set.Icc (0 : Fl g) 1)) :=
      (isCompact_Icc.image (continuous_per A)).image hd.continuous
    refine hK.isBounded.subset ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx, l, hl, rfl⟩ := GlobalTheory.FundDom.fund_dom A hA z
    exact ⟨per A x, ⟨x, hx, rfl⟩, (hpe l hl _).symm⟩
  have := hd.apply_eq_apply_of_bounded hb z 0
  simpa [hh] using this

theorem fibre_exp {g : ℕ} {A : Matrix (Fin g) (Fin g) ℂ} (hA : (A.map Complex.im).det ≠ 0)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0)
    (hper : ∀ l ∈ stdLat g, ∃ c : ℂ, ∀ z, f (z + per A l) = c * f z) (z : Fin g → ℂ) :
    f z = f 0 * Complex.exp ((fun k => (f 0)⁻¹ * fderiv ℂ f 0 (Pi.single k 1)) ⬝ᵥ z) := by
  set L := fderiv ℂ f 0
  set M : (Fin g → ℂ) →L[ℂ] ℂ := (f 0)⁻¹ • L with hM
  have hD : ∀ z, fderiv ℂ f z = (f z / f 0) • L := by
    intro z
    have e1 : HasFDerivAt (fun w => f (z + w)) (fderiv ℂ f z) 0 := by
      have h2 : HasFDerivAt (fun w : Fin g → ℂ => z + w) (ContinuousLinearMap.id ℂ _) 0 :=
        (hasFDerivAt_id (0 : Fin g → ℂ)).const_add z
      have h1 : HasFDerivAt f (fderiv ℂ f z) (z + 0) := by
        rw [add_zero]; exact (hf z).hasFDerivAt
      exact h1.comp (0 : Fin g → ℂ) h2
    have e2 : HasFDerivAt (fun w => (f z / f 0) * f w) ((f z / f 0) • L) 0 :=
      (hf 0).hasFDerivAt.const_mul _
    have heq : (fun w => f (z + w)) = fun w => (f z / f 0) * f w := by
      funext w
      have := quot_const hA hf hf0 hper w z
      rw [div_eq_div_iff (hf0 z) (hf0 0)] at this
      field_simp [hf0 0]
      linear_combination this
    rw [heq] at e1
    exact e1.unique e2
  set k : (Fin g → ℂ) → ℂ := fun z => f z * Complex.exp (-(M z)) with hk
  have hkd : ∀ z, HasFDerivAt k (0 : (Fin g → ℂ) →L[ℂ] ℂ) z := by
    intro z
    have h3 := (hf z).hasFDerivAt.mul (M.hasFDerivAt.neg.cexp)
    have hk' : k = (f * fun x => Complex.exp ((-⇑M) x)) := by
      funext x; simp [hk]
    rw [hk']
    refine h3.congr_fderiv ?_
    rw [hD z]
    ext v
    simp [hM, L]
    field_simp [hf0 0]
    ring
  have hkc : k z = k 0 := by
    have hdk : Differentiable ℂ k := fun z => (hkd z).differentiableAt
    exact is_const_of_fderiv_eq_zero hdk (fun z => (hkd z).fderiv) z 0
  have hMz : M z = (fun k => (f 0)⁻¹ * L (Pi.single k 1)) ⬝ᵥ z := by
    conv_lhs => rw [pi_eq_sum_univ z]
    simp [hM, dotProduct, map_sum, mul_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 3
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [hk, map_zero, neg_zero, Complex.exp_zero, mul_one] at hkc
  rw [← hMz, ← hkc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem exp_linear_of_quasiPeriodic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ →
    ∀ (c : Fl g → E → ℂ) (ψ : Pt E g → ℂ), DifferentiableOn ℂ ψ (cov U g) →
    (∀ P ∈ cov U g, ψ P ≠ 0) → (∀ l ∈ stdLat g, ∀ P ∈ cov U g, ψ (transl τ l P) = c l P.1 * ψ P) →
    ∃ a : E → Fin g → ℂ, DifferentiableOn ℂ a U ∧
      ∀ P ∈ cov U g, ψ P = ψ (P.1, 0) * Complex.exp (a P.1 ⬝ᵥ P.2) := by
  intro g E _ _ _ U τ hτ c ψ hψ hψ0 hper
  have hcov : IsOpen (cov U g) := hτ.1.prod isOpen_univ
  have hmem : ∀ b ∈ U, ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov U g := fun b hb _ => ⟨hb, trivial⟩
  have hslice : ∀ b ∈ U, Differentiable ℂ (fun z : Fin g → ℂ => ψ (b, z)) := fun b hb z =>
    ((hψ (b, z) (hmem b hb z)).differentiableAt (hcov.mem_nhds (hmem b hb z))).comp z
      ((differentiableAt_const b).prodMk differentiableAt_id)
  have hpd : ∀ b ∈ U, ∀ v : Fin g → ℂ,
      fderiv ℂ (fun z : Fin g → ℂ => ψ (b, z)) 0 v = fderiv ℂ ψ (b, 0) (0, v) := by
    intro b hb v
    have h1 : HasFDerivAt ψ (fderiv ℂ ψ (b, 0)) (b, 0) :=
      ((hψ _ (hmem b hb 0)).differentiableAt (hcov.mem_nhds (hmem b hb 0))).hasFDerivAt
    have h2 : HasFDerivAt (fun z : Fin g → ℂ => ((b, z) : Pt E g))
        ((0 : (Fin g → ℂ) →L[ℂ] E).prod (ContinuousLinearMap.id ℂ _)) 0 :=
      (hasFDerivAt_const b 0).prodMk (hasFDerivAt_id 0)
    have h3 : HasFDerivAt (fun z : Fin g → ℂ => ψ (b, z))
        ((fderiv ℂ ψ (b, 0)).comp ((0 : (Fin g → ℂ) →L[ℂ] E).prod (ContinuousLinearMap.id ℂ _))) 0 :=
      h1.comp (0 : Fin g → ℂ) h2
    rw [h3.fderiv]
    simp
  refine ⟨fun b k => (ψ (b, 0))⁻¹ * fderiv ℂ ψ (b, 0) (0, Pi.single k 1), ?_, ?_⟩
  · have han := GlobalTheory.ThetaMetSmooth.analyticOnNhd_of_differentiableOn hcov hψ
    have hD : DifferentiableOn ℂ (fderiv ℂ ψ) (cov U g) := han.fderiv.differentiableOn
    have hinc : DifferentiableOn ℂ (fun b : E => ((b, 0) : Pt E g)) U :=
      (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    have hmaps : Set.MapsTo (fun b : E => ((b, 0) : Pt E g)) U (cov U g) := fun b hb => hmem b hb 0
    refine differentiableOn_pi.2 fun k => ?_
    exact ((hψ.comp hinc hmaps).inv fun b hb => hψ0 _ (hmem b hb 0)).mul
      ((hD.comp hinc hmaps).clm_apply (differentiableOn_const _))
  · rintro ⟨b, z⟩ ⟨hb, -⟩
    have hA : ((τ b).map Complex.im).det ≠ 0 := (hτ.2.2 b hb).2.det_pos.ne'
    have key := fibre_exp hA (hslice b hb) (fun z => hψ0 _ (hmem b hb z))
      (fun l hl => ⟨c l b, fun z => hper l hl (b, z) (hmem b hb z)⟩) z
    simp only at key ⊢
    rw [key]
    congr 3
    funext k
    rw [hpd b hb]

end GlobalTheory.QuasiPeriodicExp
