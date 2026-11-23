import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

namespace GlobalTheory.RatValPull

theorem map_fnOf {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G] (π : G ⟶ X)
    (φ : X.functionField →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint G ∈ π ⁻¹ᵁ U) (a : Γ(X, U)) :
    φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a) := by
  have hl : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ :
      X.presheaf.stalk (genericPoint X) ⟶ G.presheaf.stalk (genericPoint G))) :=
    inferInstanceAs (IsLocalHom φ)
  have key : ∀ (g g' : Spec (G.presheaf.stalk (genericPoint G)) ⟶ X) (e : g = g')
      (hg : g (IsLocalRing.closedPoint _) ∈ U) (hg' : g' (IsLocalRing.closedPoint _) ∈ U),
      X.presheaf.germ U _ hg ≫ Scheme.stalkClosedPointTo g =
        X.presheaf.germ U _ hg' ≫ Scheme.stalkClosedPointTo g' := by
    rintro g _ rfl _ _; rfl
  have h₀ : G.fromSpecStalk (genericPoint G) (IsLocalRing.closedPoint _) ∈ π ⁻¹ᵁ U := by
    rw [Scheme.fromSpecStalk_closedPoint]; exact h'
  have h₁ : (G.fromSpecStalk (genericPoint G) ≫ π) (IsLocalRing.closedPoint _) ∈ U := h₀
  have h₂ := h₁
  rw [φs] at h₂
  have e := key _ _ φs h₁ h₂
  have e₂ := @Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk X
    (G.presheaf.stalk (genericPoint G)) _ (genericPoint X) (CommRingCat.ofHom φ) hl U h₂
  have e₁ : X.presheaf.germ U _ h₁ ≫
      Scheme.stalkClosedPointTo (G.fromSpecStalk (genericPoint G) ≫ π) =
      π.app U ≫ G.presheaf.germ (π ⁻¹ᵁ U) _ h' := by
    rw [Scheme.stalkClosedPointTo_comp, Scheme.stalkClosedPointTo_fromSpecStalk]
    erw [Scheme.Hom.germ_stalkMap_assoc π U _ h₀]
    congr 1
    exact G.presheaf.germ_stalkSpecializes _
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint.symm)
  have e₃ := (e₁.symm.trans e).trans e₂
  exact (congrArg (fun m => CommRingCat.Hom.hom m a) e₃).symm

theorem regAt_ratVal_pull : ∀ {k : Type} [CommRing k] {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G] (qX : X ⟶ Sp k) (πG : G ⟶ X)
    (φ : X.functionField →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ X.fromSpecStalk (genericPoint X))
    (σ : k →+* ℂ) (z : CxPts (πG ≫ qX) σ) (y : CxPts qX σ), y.1 = z.1 ≫ πG → ∀ f : X.functionField,
    (RegAt (under y) f → RegAt (under z) (φ f) ∧ ratVal (φ f) z = ratVal f y) ∧
      (UnitAt (under y) f → UnitAt (under z) (φ f)) := by
  intro k _ X G _ _ qX πG φ φs σ z y hy f
  have hu : under y = πG (under z) := by
    change y.1 _ = _
    rw [hy]; rfl
  have hm : ∀ {U : X.Opens}, under y ∈ U → under z ∈ πG ⁻¹ᵁ U := fun {U} hU => by
    rw [hu] at hU; exact hU
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    rw [map_fnOf πG φ φs U _ (gen_mem (hm hU))]
    refine ⟨regAt_fnOf (hm hU) _ _, ?_⟩
    rw [ratVal_fnOf (mem_ptsIn.2 (hm hU)), ratVal_fnOf (mem_ptsIn.2 hU)]
    change valR z.1 _ _ = valR y.1 _ _
    rw [hy]
    exact (GlobalTheory.Points.valR_comp z.1 πG U a).symm
  · obtain ⟨U, hU, a, rfl⟩ := hf.regAt.exists_fnOf
    rw [map_fnOf πG φ φs U _ (gen_mem (hm hU)), unitAt_fnOf_iff (hm hU),
      ← Scheme.preimage_basicOpen]
    exact hm ((unitAt_fnOf_iff hU _ a).1 hf)

end GlobalTheory.RatValPull
