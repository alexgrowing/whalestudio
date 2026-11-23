import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSLoc

theorem leibniz_frac {B C : Type} [CommRing B] [CommRing C] (ψ : B →+* C) (d : C → C)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ B B) {b u r : B} (hu : IsUnit u)
    (h : b * u = r) (h₁ : d (ψ u) = ψ (D u)) (h₂ : d (ψ r) = ψ (D r)) : d (ψ b) = ψ (D b) := by
  subst h
  rw [map_mul, hd, h₁, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul] at h₂
  exact (hu.map ψ).mul_left_cancel (add_left_cancel h₂)

theorem exists_frac {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1))
    (hf : W.1 = X.basicOpen f) (b : Γ(X, W.1)) :
    ∃ u r : Γ(X, U.1), IsUnit ((X.presheaf.map (homOfLE hW).op).hom u) ∧
      b * (X.presheaf.map (homOfLE hW).op).hom u = (X.presheaf.map (homOfLE hW).op).hom r := by
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have hl : IsLocalization.Away f Γ(X, W.1) := U.2.isLocalization_of_eq_basicOpen f (homOfLE hW) hf
  obtain ⟨⟨r, u⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
  exact ⟨u.1, r, IsLocalization.map_units Γ(X, W.1) u, h⟩

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE hW).op

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r)) → GlobalTheory.LogKS.IsKS t V U v D Θ → GlobalTheory.LogKS.IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  intro E _ _ _ H X t V U W hW f hf n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    have key : ∀ r : Γ(X, U.1), d i _ ((t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r)) = (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        (DW ((X.presheaf.map (homOfLE hW).op).hom r)) := by
      intro r
      rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
    obtain ⟨u, r, hu, hb⟩ := exists_frac U W hW f hf b
    exact leibniz_frac _ _ ((hfld i).2.1 _ inf_le_left) DW hu hb (key u) (key r)
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← spMap_res_chart U W hW, ← Category.assoc, spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp', dualMap_comp']

end GlobalTheory.LogKSLoc
