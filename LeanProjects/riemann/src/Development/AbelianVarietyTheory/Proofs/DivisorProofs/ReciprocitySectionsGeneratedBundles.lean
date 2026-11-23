import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.RecSec

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem finsum_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i (A.tens C)) (B.logSec b) z =
      ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i A) (B.logSec b) z +
        ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i C) (B.logSec b) z := by
  have : CompactSpace X := compactSpace_of_projOver hp
  have hfin := Δ.finite_support_mult
  have hsub (G : X → ℝ) : (Function.support fun z => (Δ.mult z : ℝ) * G z).Finite :=
    hfin.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h0; exact hz (by simp [h0])
  rw [← finsum_add_distrib (hsub _) (hsub _)]
  refine finsum_congr fun z => ?_
  by_cases h0 : Δ.mult z = 0
  · simp [h0]
  have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
  have hcl : topologicalKrullDim (closure ({z} : Set X)) = e :=
    (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hz1
  have h₁ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i A) z hcl).2.2.2 B b (hb z h0)
  have h₂ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i C) z hcl).2.2.2 B b (hb z h0)
  rw [GlobalTheory.T.pointClosureIntegral_update_tensor_additive F X p σ hp e L i A C (B.logSec b) z h₁ h₂, mul_add]

theorem side_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (N M : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    side N (Function.update L i (A.tens C)) (M.logSec s) (B.logSec b) Δ =
      side N (Function.update L i A) (M.logSec s) (B.logSec b) Δ +
        side N (Function.update L i C) (M.logSec s) (B.logSec b) Δ := by
  simp only [side, Fin.cons_update]
  have hA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ A) M s hs
  have hC := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ C) M s hs
  rw [(GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hp (e + 1) (Fin.cons N L) i.succ A C (M.logSec s) hA hC).2,
    finsum_update_tens P hp hdim Δ B b hb L i A C]
  ring

theorem reciprocity_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro P F _ X _ _ p σ e hp hdim L M N s hs t ht hcod hgM hgN
  classical
  let Df : (Fin e → MLine p σ) → ℝ := fun L =>
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) -
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)
  have hbt : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_left fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hbs : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_right fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hadd : ∀ (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ),
      Df (Function.update L i (A.tens C)) = Df (Function.update L i A) + Df (Function.update L i C) := by
    intro L i A C
    simp only [Df, side_update_tens P hp hdim N M s hs _ N t hbt L i A C,
      side_update_tens P hp hdim M N t ht _ M s hbs L i A C]
    ring
  have hpos : ∀ L : Fin e → MLine p σ, (∀ i, (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := fun L hL =>
    sub_eq_zero.2 (GlobalTheory.T.generatedBundles_reciprocity_semiPositive P F X p σ e hp hdim L M N s hs t ht hcod hL hgM hgN)
  have key : ∀ (S : Finset (Fin e)) (L : Fin e → MLine p σ),
      (∀ i, i ∉ S → (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun L hL => hpos L fun i => hL i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro L hL
      obtain ⟨Q, hQ, hAQ⟩ := GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle F X p σ hp (e + 1) (L a)
      have hgood : ∀ R : MLine p σ, R.φ.SemiPosReg (e + 1) → Df (Function.update L a R) = 0 := by
        intro R hR
        refine ih _ fun i hi => ?_
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hR
        · rw [Function.update_of_ne hia]
          exact hL i (by simp [hia, hi])
      have h := hadd L a (L a) Q
      rw [hgood _ hAQ, hgood _ hQ, Function.update_eq_self] at h
      linarith
  have := key Finset.univ L fun i hi => absurd (Finset.mem_univ i) hi
  exact sub_eq_zero.1 this

end GlobalTheory.RecSec
