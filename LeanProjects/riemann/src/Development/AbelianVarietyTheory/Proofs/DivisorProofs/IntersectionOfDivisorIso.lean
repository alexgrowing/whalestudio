import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry.Deg

open GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {F : Type} [Field F] {Y Y' : Var F}

theorem eq_functionFieldMap {f : Y.X ⟶ Y'.X} [IsDominant f] {ψ : Y'.Fn →+* Y.Fn}
    (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') (a : Y'.Fn) : ψ a = GlobalTheory.functionFieldMap f a := by
  have e : ψ = GlobalTheory.functionFieldMap f :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Y'.X.presheaf.stalk (f (genericPoint Y.X)))) (RingHom.ext fun z =>
      (map_alg h _ z).trans (GlobalTheory.functionFieldMap_algebraMap f _ z).symm)
  rw [e]

theorem eq_pullback_add {Δ : Y.Dv} {Δ' : Y'.Dv} {φ : Y.X ≅ Y'.X} {ψ : Y'.Fn →+* Y.Fn} {u : Y.Fnˣ}
    (h : DivIso Δ Δ' φ ψ u) : Δ = DomPull.pullback φ.hom Δ' + principal u := by
  refine ext_of_isEqn fun y => ?_
  obtain ⟨g, hg⟩ := Δ'.exists_isEqn (φ.hom y)
  refine ⟨_, h.2.2.2 y g hg, ?_⟩
  have e : Units.map (ψ : Y'.Fn →* Y.Fn) g = DomPull.unitsMap φ.hom g :=
    Units.ext (eq_functionFieldMap h.2.1 _)
  rw [e]
  exact (DomPull.isEqn_pullback φ.hom Δ' hg).add (isEqn_principal u y)

theorem topSelf_pull (φ : Y.X ≅ Y'.X) (hφ : φ.hom ≫ Y'.str = Y.str) {M : LB Y'.X} (hM : M.IsLB) (d : ℕ) :
    topSelfIntersection F (M.pull φ.hom) d = topSelfIntersection F M d := by
  rw [← interNumOn_const_eq_topSelf (appTop_algebraΓOfHom φ.hom Y'.str hφ) hM d, topSelf_def, ← interNumOn_id,
    ← interNumOn_comp_of_isIso F φ.hom (𝟙 Y'.X), Category.comp_id]

theorem inter_eq_of_divIso : ∀ (F : Type) [Field F] (Y Y' : Var F) (Δ : Y.Dv) (Δ' : Y'.Dv) (φ : Y.X ≅ Y'.X)
    (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ), DivIso Δ Δ' φ ψ u → Y.inter (fun _ => Δ) = Y'.inter (fun _ => Δ') := by
  intro F _ Y Y' Δ Δ' φ ψ u h
  have e : toPic Δ = cls _ (DomPull.presents_pullback φ.hom Δ').isLB := by
    rw [eq_pullback_add h, map_add, toPic_principal, add_zero]
    exact (DomPull.presents_pullback φ.hom Δ').toPic_eq
  rw [Var.inter_eq_of_toPic_eq (fun _ => (DomPull.presents_pullback φ.hom Δ').isLB) fun _ => e, Var.inter_const,
    ← h.2.2.1]
  exact topSelf_pull φ h.1 (isLB_toLB Δ') Y.dim

end GlobalTheory.ShFam.GalCarry.Deg
