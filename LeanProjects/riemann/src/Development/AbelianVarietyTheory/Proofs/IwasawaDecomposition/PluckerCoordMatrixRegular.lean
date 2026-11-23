import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.FlagAmple.PlkLoc
theorem fnOf_eq_algebraMap_germ {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (y : X) (hy : y ∈ U)
    (h : genericPoint X ∈ U) :
    fnOf U h = (algebraMap (X.presheaf.stalk y) X.functionField).comp (X.presheaf.germ U y hy).hom := by
  have e := X.presheaf.germ_stalkSpecializes hy ((genericPoint_spec X).specializes trivial)
  ext a
  rw [fnOf, RingHom.comp_apply, ← e]
  rfl

theorem fromSpecStalk_comp_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V) (y : X)
    (hy : y ∈ f ⁻¹ᵁ V) :
    X.fromSpecStalk y ≫ f = Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl ≫ X.presheaf.germ (f ⁻¹ᵁ V) y hy) ≫ hV.fromSpec := by
  have hy' : f y ∈ V := hy
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hV.fromSpecStalk_eq_fromSpecStalk hy']
  change Spec.map _ ≫ Spec.map (Y.presheaf.germ V (f y) hy') ≫ hV.fromSpec = _
  rw [← Category.assoc, ← Spec.map_comp, Scheme.Hom.germ_stalkMap f V y hy', Scheme.Hom.app_eq_appLE]

set_option maxHeartbeats 1000000 in

theorem exists_tri_mul_unit_of_coord : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → ∀ y : (Φ.C k).Y.X, y ∈ (Φ.C k).π ⁻¹ᵁ V → ∃ (t : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Φ.C k).Y.Fnˣ) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn) (By : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)), (∀ τ a, ((Φ.C k).gr τ a).IsEqn y (t τ a)) ∧ (∀ τ a, T τ a a = t τ a) ∧ (∀ τ (a b : Fin (S.Dw.mult τ)), a < b → T τ a b = 0) ∧ (∀ τ, IsUnit (By τ)) ∧ ∀ τ, B τ = T τ * (By τ).map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) := by
  intro D A N j S κ s Φ k V hV φ g _hstr _hstab hne B hB y hy
  let ψ : Γ(gen s.T.Z, V) →+* (Φ.C k).Y.X.presheaf.stalk y :=
    ((Φ.C k).π.appLE V ((Φ.C k).π ⁻¹ᵁ V) le_rfl ≫ (Φ.C k).Y.X.presheaf.germ ((Φ.C k).π ⁻¹ᵁ V) y hy).hom
  have h1 : baseFn (Φ.C k) V hne = (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn).comp ψ := by
    rw [baseFn, fnOf_eq_algebraMap_germ _ y hy hne]
    rfl
  have h2 : stalkPt (Φ.C k).Y y ≫ (Φ.C k).π = spMap ψ ≫ hV.fromSpec := by
    exact fromSpecStalk_comp_eq (Φ.C k).π V hV y hy
  clear_value ψ
  obtain ⟨φy, fy, t, hT, hE⟩ := (Φ.C k).gr_spec y
  have hinj := IsFractionRing.injective ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField
  have h3 : φy = ψ.comp φ := by
    ext a
    apply hinj
    have e1 := RingHom.congr_fun hT.2.1 a
    have e2 := RingHom.congr_fun hB.2.1 a
    rw [h1] at e2
    exact e1.symm.trans e2
  have hx : stalkPt (Φ.C k).Y y ≫ (Φ.C k).π ≫ genι s.T.Z = spMap ψ ≫ hV.fromSpec ≫ genι s.T.Z := by
    rw [← Category.assoc, h2, Category.assoc]
  obtain ⟨gy, hgy⟩ := g.exists_isMap ψ h3 hx
  obtain ⟨gF, hgF⟩ := gy.exists_isMap (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField) hT.2.1 hT.1
  obtain ⟨fF, hfF⟩ := fy.exists_isMap (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.X.functionField) hT.2.1 hT.1
  have hB' : ∀ τ, gF.co (Φ.C k).f0 τ = (B τ)ᵀ := fun τ =>
    GlobalTheory.ShFam.EigFrame.co_eq fun i => by
      have h := hB.2.2 τ i
      have hv : gF.v τ = fun k' => spMap (dualMap (baseFn (Φ.C k) V hne)) ≫ g.v τ k' := by
        funext k'
        rw [hgF τ k', hgy τ k', h1]
        exact GradedPieces.dual_comp ψ _ _
      rw [hv]
      exact h
  refine ⟨t, fun τ => (fF.co (Φ.C k).f0 τ)ᵀ, fun τ => (gy.co fy τ)ᵀ, hE, fun τ a => (hT.co τ hfF).2 a,
    fun τ a b hab => (hT.co τ hfF).1 b a hab, fun τ => ?_, fun τ => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact gy.isUnit_det_co fy τ
  · have e := gF.co_mul fF (Φ.C k).f0 τ
    rw [hB' τ, hgF.co τ hfF hT.1] at e
    rw [← Matrix.transpose_transpose (B τ), ← e, Matrix.transpose_mul, Matrix.transpose_map]

end GlobalTheory.FlagAmple.PlkLoc
