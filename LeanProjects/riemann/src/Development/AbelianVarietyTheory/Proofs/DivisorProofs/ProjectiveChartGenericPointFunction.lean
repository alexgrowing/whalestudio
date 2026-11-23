import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsSumPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterShiftLeOfBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompHt

open GlobalTheory.ProjSpace in

theorem mem_genericPrime_iff {R : Type} [CommRing R] {m : ℕ} {X : Scheme.{0}} [IsIntegral X]
    (π : X ⟶ PSpace R m) (i : Fin (m + 1)) (U : X.Opens) (hη : genericPoint X ∈ U)
    (hU : U ≤ π ⁻¹ᵁ chart R m i) {d : ℕ} {F : MvPolynomial (Fin (m + 1)) R} (hF : F.IsHomogeneous d) :
    F ∈ (π (genericPoint X) : ProjectiveSpectrum
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)).asHomogeneousIdeal.toIdeal ↔
      MvPolynomial.eval₂ (GlobalTheory.Cartier.constFn (π ≫ PSpace.str R m)) (fun j => fnOf U hη (pullRatio π U i hU j)) F = 0 := by
  have e₁ := congrArg (fun t => t F) (appLE_comp_aeval_ratio (φ := π) (hi := hU))
  have e₂ : (π.appLE (chart R m i) U hU).hom (formOn (chart R m i) i le_rfl d F hF) =
      MvPolynomial.eval₂ (algX (π ≫ PSpace.str R m) U) (pullRatio π U i hU) F := by
    rw [formOn_eq_aeval]
    exact e₁
  have e₃ : fnOf U hη ((π.appLE (chart R m i) U hU).hom (formOn (chart R m i) i le_rfl d F hF)) =
      MvPolynomial.eval₂ (GlobalTheory.Cartier.constFn (π ≫ PSpace.str R m)) (fun j => fnOf U hη (pullRatio π U i hU j)) F := by
    rw [e₂, MvPolynomial.eval₂_comp_left, fnOf_comp_algX]
    rfl
  have e₄ : X.basicOpen ((π.appLE (chart R m i) U hU).hom (formOn (chart R m i) i le_rfl d F hF)) =
      U ⊓ π ⁻¹ᵁ (chart R m i ⊓ Proj.basicOpen (grading R m) F) := by
    refine (Scheme.basicOpen_appLE π U _ hU _).trans ?_
    rw [basicOpen_formOn]
  have e₅ := X.mem_basicOpen ((π.appLE (chart R m i) U hU).hom (formOn (chart R m i) i le_rfl d F hF))
    (genericPoint X) hη
  rw [e₄] at e₅
  have e₆ : genericPoint X ∈ U ⊓ π ⁻¹ᵁ (chart R m i ⊓ Proj.basicOpen (grading R m) F) ↔
      IsUnit (fnOf U hη ((π.appLE (chart R m i) U hU).hom (formOn (chart R m i) i le_rfl d F hF))) := e₅
  rw [e₃, isUnit_iff_ne_zero] at e₆
  rw [← not_iff_not]
  exact Iff.trans ⟨fun h => ⟨hη, hU hη, h⟩, fun h => h.2.2⟩ e₆

theorem map_genericPrime_eq_coneIdeal : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (π : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField) (i : Fin (m + 1)) (U : X.Opens) (hη : genericPoint X ∈ U) (hU : U ≤ π ⁻¹ᵁ GlobalTheory.ProjSpace.chart (𝓞 K) m i),
    π ≫ PSpace.str (𝓞 K) m = p →
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    y i ≠ 0 → (∀ j, fnOf U hη (GlobalTheory.ProjSpace.pullRatio π U i hU j) = ψ (y j / y i)) →
    ((π (genericPoint X) : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (𝓞 K))).asHomogeneousIdeal.toIdeal).map
      (MvPolynomial.map (algebraMap (𝓞 K) K)) = GlobalTheory.CompHt.coneIdeal K y := by
  intro K Ω _ _ _ _ m y X _ p π ψ i U hη hU hp hψ hy hr
  subst hp
  set P := (π (genericPoint X) : ProjectiveSpectrum
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (𝓞 K))).asHomogeneousIdeal with hP
  have hc : GlobalTheory.Cartier.constFn (π ≫ PSpace.str (𝓞 K) m) = ψ.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) :=
    RingHom.ext fun a => (hψ a).symm
  have hs : (fun j => y j / y i) = (y i)⁻¹ • y := funext fun j => by
    simp [div_eq_inv_mul]
  have key : ∀ {d : ℕ} {F : MvPolynomial (Fin (m + 1)) (𝓞 K)}, F.IsHomogeneous d →
      (F ∈ P.toIdeal ↔ MvPolynomial.aeval y (MvPolynomial.map (algebraMap (𝓞 K) K) F) = 0) := by
    intro d F hF
    rw [hP, mem_genericPrime_iff π i U hη hU hF, ← mem_coneIdeal_of_isHomogeneous y (hF.map _),
      ← coneIdeal_smul (inv_ne_zero hy), mem_coneIdeal_of_isHomogeneous _ (hF.map _), ← hs, hc, funext hr,
      MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← map_eq_zero_iff ψ ψ.injective,
      MvPolynomial.eval₂_comp_left]
    rfl
  have hcomap : P.toIdeal = (coneIdeal K y).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    ext F
    rw [Ideal.mem_comap, mem_coneIdeal_iff, P.isHomogeneous.mem_iff]
    refine forall_congr' fun d => ?_
    have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (𝓞 K)) F d : _) :
        MvPolynomial (Fin (m + 1)) (𝓞 K)) = MvPolynomial.homogeneousComponent d F :=
      MvPolynomial.decomposition.decompose'_apply F d
    have e' : MvPolynomial.map (algebraMap (𝓞 K) K) (MvPolynomial.homogeneousComponent d F) =
        MvPolynomial.homogeneousComponent d (MvPolynomial.map (algebraMap (𝓞 K) K) F) := by
      ext a
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
      split_ifs <;> simp
    rw [e, key (MvPolynomial.homogeneousComponent_isHomogeneous d F), e']
  rw [hcomap]
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin (m + 1)) (R := 𝓞 K) (S := K)
  exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := Fin (m + 1))))
    (MvPolynomial (Fin (m + 1)) K) (coneIdeal K y)

end GlobalTheory.CompHt
