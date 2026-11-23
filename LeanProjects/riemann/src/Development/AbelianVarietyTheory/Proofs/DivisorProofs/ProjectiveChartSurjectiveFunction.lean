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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResDegRatio

theorem residue_germ_appLE_mem {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (V : Y.Opens) (U : X.Opens) (hx : x ∈ U)
    (h : U ≤ f ⁻¹ᵁ V) (s : Γ(Y, V)) :
    (X.residue x).hom ((X.presheaf.germ U x hx).hom ((f.appLE V U h).hom s)) ∈
      (f.residueFieldMap x).hom.fieldRange := by
  refine ⟨Y.evaluation V (f x) (h hx) s, ?_⟩
  refine (Scheme.evaluation_naturality_apply f x (h hx) s).trans ?_
  refine congrArg (X.residue x).hom ?_
  exact (X.presheaf.germ_res_apply (homOfLE h) x hx _).symm

theorem residueDegree_eq_one_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X)
    (hs : Function.Surjective (f.residueFieldMap x).hom) : f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have h : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective _, hs⟩
  exact (LinearEquiv.ofBijective (Algebra.linearMap _ _) h).finrank_eq.symm.trans (CommSemiring.finrank_self _)

theorem residueDegree_eq_one_of_ratios :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (z : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (π : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField) (i : Fin (m + 1)) (U : X.Opens) (hη : genericPoint X ∈ U) (hU : U ≤ π ⁻¹ᵁ GlobalTheory.ProjSpace.chart (𝓞 K) m i),
    π ≫ PSpace.str (𝓞 K) m = p → Function.Surjective ψ →
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    IntermediateField.adjoin K (Set.range z) = ⊤ → (∀ j, fnOf U hη (GlobalTheory.ProjSpace.pullRatio π U i hU j) = ψ (z j)) →
    π.residueDegree (genericPoint X) = 1 := by
  intro K Ω _ _ _ _ m z X _ p π ψ i U hη hU hp hψ hc hz hr
  subst hp
  refine residueDegree_eq_one_of_surjective π _ ?_
  let ρ : Ω →+* X.residueField (genericPoint X) := (X.residue (genericPoint X)).hom.comp ψ
  let F : Subfield Ω := ((π.residueFieldMap (genericPoint X)).hom.fieldRange).comap ρ
  have hO : ∀ a : 𝓞 K, algebraMap K Ω (a : K) ∈ F := fun a => by
    change (X.residue (genericPoint X)).hom (ψ _) ∈ (π.residueFieldMap (genericPoint X)).hom.fieldRange
    rw [hc]
    have e : algX (π ≫ PSpace.str (𝓞 K) m) ⊤ a =
        (π.appLE ⊤ ⊤ le_top).hom (algX (PSpace.str (𝓞 K) m) ⊤ a) :=
      (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).inv.hom a))
        (Scheme.Hom.appLE_comp_appLE π (PSpace.str (𝓞 K) m) ⊤ ⊤ ⊤ le_top le_top)).symm
    rw [e]
    exact residue_germ_appLE_mem π _ ⊤ ⊤ _ le_top _
  have hK : ∀ a : K, algebraMap K Ω a ∈ F := fun a => by
    obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    rw [map_div₀]
    exact F.div_mem (hO b) (hO c)
  have hF : IntermediateField.adjoin K (Set.range z) ≤ F.toIntermediateField hK := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change (X.residue (genericPoint X)).hom (ψ _) ∈ (π.residueFieldMap (genericPoint X)).hom.fieldRange
    rw [← hr]
    exact residue_germ_appLE_mem π _ _ U hη hU _
  intro y
  obtain ⟨b, rfl⟩ := X.residue_surjective (genericPoint X) y
  obtain ⟨a, rfl⟩ := hψ b
  rw [hz] at hF
  exact hF (IntermediateField.mem_top (x := a))

end GlobalTheory.ResDegRatio
