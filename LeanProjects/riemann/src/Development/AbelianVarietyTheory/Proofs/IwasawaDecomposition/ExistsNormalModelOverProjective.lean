import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModelOver

theorem isProjOver_comp_spMap {R S : Type} [CommRing R] [CommRing S] (ε : R ≃+* S) {X : Scheme.{0}} {s : X ⟶ Sp S}
    (h : IsProjOver s) : IsProjOver (s ≫ spMap ε.toRingHom) := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsIso (spMap ε.toRingHom) := by
    have : IsIso (CommRingCat.ofHom ε.toRingHom) := (ε.toCommRingCatIso).isIso_hom
    exact inferInstance
  have hb : IsIso (GlobalTheory.ProjSpace.baseChange N ε.toRingHom) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
      (GlobalTheory.ProjSpace.isPullback_baseChange N ε.toRingHom).flip ‹_›
  refine ⟨N, i ≫ GlobalTheory.ProjSpace.baseChange N ε.toRingHom, inferInstance, ?_⟩
  rw [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, Category.assoc]

theorem isSeparated_and_noetherian {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (h : IsProjOver s) : X.IsSeparated ∧ IsLocallyNoetherian X := by
  have := CommonModel.isProper_of_isProjOver h
  have hs : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from s]
    infer_instance
  exact ⟨⟨hs⟩, LocallyOfFiniteType.isLocallyNoetherian s⟩

theorem exists_normal_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] (ε : 𝓞 F ≃+* O) (X : Scheme.{0}) (sX : X ⟶ Sp O) (ρ : Y.X ⟶ X), IsProjOver sX → ρ ≫ sX ≫ spMap ε.toRingHom = Y.str ≫ spMap (algebraMap (𝓞 F) F) → X.IsSeparated ∧ IsLocallyNoetherian X ∧ ∃ (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X ∧ M.j ≫ ρ' = ρ := by
  intro F _ _ Y O _ ε X sX ρ hX hρ
  have hP := isProjOver_comp_spMap ε hX
  obtain ⟨hs, hn⟩ := isSeparated_and_noetherian hP
  refine ⟨hs, hn, ?_⟩
  obtain ⟨X', π, j, hXi, hπ, hfl, H, hg⟩ := GlobalTheory.IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver
    (fun _ : Unit => X) (fun _ => sX ≫ spMap ε.toRingHom) (fun _ => ρ) (fun _ => hP) (fun _ => hρ)
  obtain ⟨g, hg₁, -⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hXi, hπ, inferInstance,
    GlobalTheory.IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let M : GlobalTheory.TrueGeo.Model Y := ⟨X', π, har, j, H⟩
  obtain ⟨N, π₁, -, hN, -, -, hj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  refine ⟨N, π₁ ≫ g, hN, ?_⟩
  rw [← Category.assoc, hj]
  exact hg₁

end GlobalTheory.ModelOver
