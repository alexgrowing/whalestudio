import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_gPt_of_stalk : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsLocalHom j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ c : M.O x, ((ev (j ((M.stalkEquiv x).symm c)) : OO p) : PadicAlgCl p) = M.val (gPt p ≫ y) (c : Ω) := by
  intro o Ω _ _ _ M x R _ _ j _ p _ y ev hy c
  have hsp : ∀ w, (spMap j ≫ M.Z.fromSpecStalk x) w ⤳ x := fun w => by
    have : M.Z.fromSpecStalk x (spMap j w) ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  obtain ⟨U, hx, f, hf⟩ := M.Z.presheaf.germ_exist ((M.stalkEquiv x).symm c)
  have hc : c = ⟨valF M.pt U f, RatModel.valF_mem_O hx f⟩ := by
    rw [← RatModel.stalkEquiv_germ hx, hf, RingEquiv.apply_symm_apply]
  have hU : ⊤ ≤ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => (hsp w).mem_open U.isOpen hx
  have hU0 : ⊤ ≤ M.Z.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : M.Z.fromSpecStalk x w ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hx
  have hg : gPt p ≫ y = spMap ((OO p).subtype.comp ev) ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [← hy, ← Category.assoc]
    congr 1
    rw [gPt, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hU' : ⊤ ≤ (gPt p ≫ y) ⁻¹ᵁ U := by
    rw [hg]; exact fun w _ => hU (x := spMap ((OO p).subtype.comp ev) w) trivial
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hU') (f := f) (hc ▸ rfl), GlobalTheory.Points.valF_eq_valR, hg,
    GlobalTheory.Points.valR_spMap_comp _ _ U hU]
  have e1 : valR (spMap j ≫ M.Z.fromSpecStalk x) U f = j (valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f) :=
    GlobalTheory.Points.valR_spMap_comp (C := M.Z.presheaf.stalk x) j (M.Z.fromSpecStalk x) U hU0 f
  have e2 : valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f = M.Z.presheaf.germ U x hx f := by
    have eA : (M.Z.fromSpecStalk x).appLE U ⊤ hU0 =
        M.Z.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (M.Z.presheaf.stalk x)).inv := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
      simp only [Category.assoc, ← Functor.map_comp]
      have e : ((homOfLE le_top).op ≫ (homOfLE hU0).op :
          Opposite.op (⊤ : (Spec (M.Z.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
      rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
    unfold valR
    erw [dif_pos hU0, eA]
    simp only [CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  rw [e1]
  exact (congrArg (fun t => ((OO p).subtype.comp ev) (j t)) (e2.trans hf)).symm

end GlobalTheory.Poinc.TestAtPt
