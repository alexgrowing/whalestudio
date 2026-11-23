import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem etale_of_killed_tangent_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  intro p _ D R _ b N w0 r S _ s o H i hfin hflat hkill hrep htan
  haveI := hfin
  haveI := hflat
  haveI : LocallyOfFinitePresentation H.hom := inferInstance
  have hinv : ∀ {T : Over S} (a : T ⟶ o.A) (f : o.A ⟶ o.A) [IsMonHom f], a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro T a f _
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_comp, inv_mul_cancel, one_comp]
  haveI : FormallyUnramified H.hom := by
    refine TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw => ?_
    let x : Sp k ⟶ S := TangentCrit.dualPt k ≫ w ≫ H.hom
    let W : epsPtR x ⟶ H := Over.homMk w hw
    let U : epsPtR x ⟶ H := Over.homMk (TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w)
      (by simp only [Category.assoc]; rfl)
    let e : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (TangentCrit.dualPt_dualBase_assoc k _)
    have heU : e ≫ W = e ≫ U := by
      ext1
      exact (TangentCrit.dualPt_dualBase_assoc k (TangentCrit.dualPt k ≫ w)).symm
    have hv : (W ≫ i) * (U ≫ i)⁻¹ = 1 := by
      refine htan k x _ ?_ ?_
      · have h1 : e ≫ ((W ≫ i) * (U ≫ i)⁻¹) = 1 := by
          rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, heU, mul_inv_cancel]
        exact congrArg (fun q => q.left) h1
      · intro c hc
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        rw [mul_comp, hinv, Category.assoc, Category.assoc, hkill c hc, comp_one, comp_one, inv_one, _root_.mul_one]
    have hWU : W ≫ i = U ≫ i := mul_inv_eq_one.1 hv
    have hk : ∀ c ∈ w0 ^ r, (W ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, hkill c hc, comp_one]
    obtain ⟨y, -, hy⟩ := hrep _ (W ≫ i) hk
    have hW := hy W rfl
    have hU := hy U hWU.symm
    exact congrArg (fun q => q.left) (hW.trans hU.symm)
  exact Etale.of_formallyUnramified_of_flat H.hom

end GlobalTheory.UPel.HT.EtLev
