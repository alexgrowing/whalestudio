import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CTEqConjTranspose

open Matrix NumberField Module Formalism.BasicNotions

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefH

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def ctau (S : HSpace E) (τ : E →+* ℂ) (x : S.V) : Fin S.rank → ℂ := fun i => τ (S.frame.repr x i)

theorem hT_coord (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, starRingEnd_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [HSpace.gram, RingHom.id_apply]
  ring

theorem tau_hT (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x y : S.V) :
    τ (S.hT x y) = star (ctau S τ x) ⬝ᵥ ((S.gram.map τ) *ᵥ ctau S τ y) := by
  rw [hT_coord]
  simp only [dotProduct, mulVec, ctau, map_sum, map_mul, hτ, Pi.star_apply, Matrix.map_apply,
    Finset.mul_sum, Complex.star_def]

theorem hT_span_zero (S : HSpace E) {ι : Type} (f : ι → S.V) (y : S.V) (h : ∀ i, S.hT (f i) y = 0) :
    ∀ x ∈ Submodule.span E (Set.range f), S.hT x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact h i
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

theorem card_le_of_nonpos (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsig : Formalism.UG.HasSignature (S.gram.map τ) (S.sig τ).1 (S.sig τ).2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → S.V) (hv : LinearIndependent E v)
    (horth : ∀ a b, a ≠ b → S.hT (v a) (v b) = 0) (hnp : ∀ a, (τ (S.hT (v a) (v a))).re ≤ 0) :
    Fintype.card ι ≤ (S.sig τ).2 := by
  apply WbDefC.sigNeg_card_le (S.gram.map τ) _ _ hsig (fun a => ctau S τ (v a))
  · have hc : LinearIndependent E (fun a => fun i => S.frame.repr (v a) i) := by
      have := hv.map' S.frame.equivFun.toLinearMap S.frame.equivFun.ker
      simpa [Function.comp_def] using this
    exact WbDefC.linIndep_map τ _ hc
  · intro d
    have h1 : ∀ a b, star (ctau S τ (v a)) ⬝ᵥ ((S.gram.map τ) *ᵥ ctau S τ (v b)) = τ (S.hT (v a) (v b)) :=
      fun a b => (tau_hT S τ hτ (v a) (v b)).symm
    have hexp : star (∑ a, d a • ctau S τ (v a)) ⬝ᵥ ((S.gram.map τ) *ᵥ ∑ a, d a • ctau S τ (v a)) =
        ∑ a, star (d a) * d a * τ (S.hT (v a) (v a)) := by
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
        dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [horth b a hb, map_zero, mul_zero])
        (by simp)]
      ring
    rw [hexp, Complex.re_sum]
    apply Finset.sum_nonpos
    intro a _
    have key : (star (d a) * d a * τ (S.hT (v a) (v a))).re =
        ((d a).re ^ 2 + (d a).im ^ 2) * (τ (S.hT (v a) (v a))).re := by
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hnp a)

theorem finrank_perp_add (S : HSpace E) {r : ℕ} (e : Fin r → S.V) (he : LinearIndependent E e) :
    finrank E (Formalism.MainNotions.S.perpS S (Submodule.span E (Set.range e))) + r = S.rank := by
  let ψ : S.V →ₗ[E] (Fin r → E) := LinearMap.pi (fun i => S.hT (e i))
  have hker : LinearMap.ker ψ = Formalism.MainNotions.S.perpS S (Submodule.span E (Set.range e)) := by
    ext y
    simp only [LinearMap.mem_ker]
    constructor
    · intro hy x hx
      refine hT_span_zero S e y (fun i => ?_) x hx
      have := congrFun hy i
      simpa [ψ] using this
    · intro hy
      funext i
      simpa [ψ] using hy (e i) (Submodule.subset_span ⟨i, rfl⟩)
  have hsurj : LinearMap.range ψ = ⊤ := by
    rw [LinearMap.range_eq_top, ← LinearMap.dualMap_injective_iff]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    let c : Fin r → E := fun i => φ (fun j => if i = j then 1 else 0)
    have hφy : ∀ y, φ (ψ y) = S.hT (∑ i, star (c i) • e i) y := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ φ (ψ y)]
      simp [ψ, map_sum, LinearMap.sum_apply, c, mul_comm, starRingEnd_apply, star_star]
    have hzero : ∑ i, star (c i) • e i = 0 := by
      apply S.nondeg.1
      intro y
      rw [← hφy]
      have := LinearMap.congr_fun hφ y
      simpa [LinearMap.dualMap_apply] using this
    have hc : ∀ i, c i = 0 := by
      intro i
      have := Fintype.linearIndependent_iff.1 he (fun i => star (c i)) hzero i
      simpa using this
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    simp [show ∀ i, φ (fun j => if i = j then 1 else 0) = 0 from hc]
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, S.rank_eq] at h
  omega

end PI.UnitaryGroupMassFormula.CntFormula.WbDefH
