import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.OmegaProjectionScalarCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeDualityFactsStatement

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitB

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk.UnitPf

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem Om'_CH (K : ℕ)
    (hK : ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0) :
    ((List.ofFn fun t : Fin (m + 1) =>
      Om' X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V))).prod) ^ K = 0 := by
  have e : (fun t : Fin (m + 1) =>
      Om' X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V))) =
      (liftR (X := X)) ∘ (fun t : Fin (m + 1) =>
        omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))) := by
    funext t
    simp only [Function.comp_apply, map_sub, liftR_smul_one, omegaP_eq]
    rfl
  rw [e, ← List.map_ofFn, ← map_list_prod, ← map_pow, hK, map_zero]

theorem aeval_CH (K : ℕ) (γ : Fin (m + 1) → ℂ) (T : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V)) :
    Polynomial.aeval T (((List.ofFn fun t : Fin (m + 1) => Polynomial.X - Polynomial.C (γ t)).prod) ^ K) =
      ((List.ofFn fun t : Fin (m + 1) => T - γ t • (1 : Module.End ℂ _)).prod) ^ K := by
  rw [map_pow, map_list_prod, List.map_ofFn]
  congr 3
  funext t
  simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one]

theorem aeval_lin (k : ℕ) (β : ℂ) (T : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V)) :
    Polynomial.aeval T ((Polynomial.X - Polynomial.C β) ^ k) = (T - β • (1 : Module.End ℂ _)) ^ k := by
  simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem cop (γ : Fin (m + 1) → ℂ) (β : ℂ) (h : ∀ t, γ t ≠ β) (K k : ℕ) :
    IsCoprime (((List.ofFn fun t : Fin (m + 1) => Polynomial.X - Polynomial.C (γ t)).prod) ^ K)
      ((Polynomial.X - Polynomial.C β) ^ k) := by
  refine IsCoprime.pow ?_
  rw [List.prod_ofFn]
  exact IsCoprime.prod_left fun t _ =>
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 (h t)).isUnit

theorem coeY_mem_Isub
    (hD : ∃ K : ℕ, ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0)
    (hfree : ∀ r, χ r ≠ χ s + 1) (G : Fin (m + 1) → (step X (χ s)).V)
    (hG : G ∈ backSub (step X (χ s)) (χ s + 1)) : coeY G ∈ Isub X := by
  obtain ⟨K, hK⟩ := hD
  rw [backSub, Module.End.mem_maxGenEigenspace] at hG
  obtain ⟨k, hk⟩ := hG
  have h0 : ((y2 X - (-(χ s + 1) - cn (m + 1)) • 1) ^ k) (coeY G) = 0 := by
    rw [← coe_pow, hk]; rfl
  have hI : ((Om' X - (-(χ s + 1) - cn (m + 1)) • 1) ^ k) (coeY G) ∈ Isub X := by
    have := diff_mem_Isub (X := X) (-(χ s + 1) - cn (m + 1)) k (coeY G)
    rwa [h0, sub_zero] at this
  obtain ⟨A, B, hAB⟩ := cop (fun t => -χ t - cn (m + 1)) (-(χ s + 1) - cn (m + 1))
    (fun t h => hfree t (by linear_combination -h)) K k
  have e := congrArg (fun q => Polynomial.aeval (Om' X) q (coeY G)) hAB
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply] at e
  rw [← e, aeval_CH, Om'_CH K hK, LinearMap.zero_apply, map_zero, zero_add, aeval_lin]
  exact aeval_mem_Isub B hI

variable (χ s) in

def phiB (hS : ScalChar X χ) : X.V →ₗ[ℂ] ↥(backSub (step X (χ s)) (χ s + 1)) :=
  (phi0 χ s hS).codRestrict (backSub (step X (χ s)) (χ s + 1)) fun v => mem_of_eig' (omega_projection_scalar_character hS v)

theorem phiB_inj (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (hfree : ∀ r, χ r ≠ χ s + 1) :
    Function.Injective (phiB χ s hS) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv' : phi0 χ s hS v = 0 := congrArg Subtype.val hv
  have h := ptr_Pr (X := X) (s := s) hS v
  have h0 : ∑ c, Pr X χ s (Pi.single c v) c = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc : Pr X χ s (Pi.single c v) = 0 := congrArg (fun G => coeY G c) hv'
    rw [hc]; rfl
  rw [h0] at h
  have hne : (kap χ s)⁻¹ * -capP χ (-χ s - 1) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (kap_ne hsimp)) (neg_ne_zero.2 (capelliPoly_ne hfree))
  exact (smul_eq_zero.1 h.symm).resolve_left hne

theorem phiB_surj (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (hfree : ∀ r, χ r ≠ χ s + 1)
    (hom : ∀ f ∈ stepSub X (χ s), om X f = (χ s - cn (m + 1)) • f)
    (hD : ∃ K : ℕ, ((List.ofFn fun t : Fin (m + 1) =>
      omD X - (-χ t - cn (m + 1)) • (1 : Module.End ℂ (Fin (m + 1) → X.V))).prod) ^ K = 0) :
    Function.Surjective (phiB χ s hS) := by
  rintro ⟨G, hG⟩
  obtain ⟨v, hv⟩ := Pr_Isub (s := s) hS (coeY_mem_Isub hD hfree G hG)
  refine ⟨v, Subtype.ext (coeY_injective (funext fun c => ?_))⟩
  change Pr X χ s (Pi.single c v) = coeY G c
  rw [← hv c]
  exact Pr_step hS hsimp _ (hom _ (show ↥(stepSub X (χ s)) from G c).2)

variable (χ s) in

def phiBk (hS : ScalChar X χ) (hB : BackStable) :
    X.V →ₗ[ℂ] (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).V := phiB χ s hS

theorem coeY_tensVd (G : Fin (m + 1) → (step X (χ s)).V) (a b : Fin (m + 1)) :
    coeY (X := X) (χ := χ) (s := s) (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd (step X (χ s)).E a b G) =
      fun c => tensE X a b (coeY G c) - if c = b then coeY G a else 0 := by
  funext c
  unfold coeY
  rw [tensVd_apply]
  split_ifs <;> rfl

theorem phiB_E (hS : ScalChar X χ) (hB : BackStable) (a b : Fin (m + 1)) (v : X.V) :
    phiBk χ s hS hB (X.E a b v) = (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).E a b (phiBk χ s hS hB v) := by
  apply Subtype.ext
  apply coeY_injective (X := X) (χ := χ) (s := s)
  funext c
  change coeY (phi0 χ s hS (X.E a b v)) c =
    coeY (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd (step X (χ s)).E a b (phi0 χ s hS v)) c
  rw [coeY_tensVd, coe_projection_scalar_character, coe_projection_scalar_character]
  dsimp only
  by_cases h : c = b
  · subst h
    rw [if_pos rfl, ← Pr_tensE, tensE_single, if_pos rfl, map_add, add_sub_cancel_right]
  · rw [if_neg h, sub_zero, ← Pr_tensE, tensE_single, if_neg (Ne.symm h), add_zero]

theorem unit_of_dualFacts (hDF : DualFacts) : Unit := by
  rintro (_ | m) X χ s hB hS hfree hsimp hom
  · exact s.elim0
  · have hH : HasChar X χ := ⟨1, fun Y => by rw [hS Y, sub_self, pow_one]⟩
    have hD := (hDF (m + 1) X χ hH).1
    obtain ⟨φ, hφ⟩ : ∃ φ : X.V ≃ₗ[ℂ] (back (step X (χ s)) (χ s + 1) (hB (m + 1) _ _)).V,
        ∀ v, φ v = phiBk χ s hS hB v :=
      ⟨LinearEquiv.ofBijective (phiBk χ s hS hB) ⟨phiB_inj hS hsimp hfree, phiB_surj hS hsimp hfree hom hD⟩,
        fun v => rfl⟩
    refine ⟨φ.symm, fun a b x => φ.injective ?_⟩
    rw [LinearEquiv.apply_symm_apply, hφ, phiB_E hS hB a b, ← hφ, LinearEquiv.apply_symm_apply]

end CompanionTheory.RgExh.Hk.UnitB

theorem unitarity : CompanionTheory.RgExh.Hk.Unit := CompanionTheory.RgExh.Hk.UnitB.unit_of_dualFacts GlobalTheory.T.HeckeDualityFacts
