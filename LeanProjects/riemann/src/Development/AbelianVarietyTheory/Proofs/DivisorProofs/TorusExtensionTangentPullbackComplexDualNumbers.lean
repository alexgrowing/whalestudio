import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanPull

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  intro V _ _ D C _ _ N ν gm₀ htan
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  have hTF : spMap (toF V C) = (TF (R := V) C).hom := by
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hTE : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    rw [TanLift.dualMap_over, hTF]; rfl
  let hh : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hTE
  obtain ⟨x₀, rfl⟩ := (Φ (epsR V)).surjective gm₀
  refine ⟨Φ _ (hh ≫ x₀), hp _ _ hh x₀, ?_, ?_, ?_⟩
  · obtain ⟨o₀, ho₀, hpo⟩ := htan
    let r : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) (TanLift.redE_over V)
    have e₀ : o₀ = Φ _ (r ≫ x₀) := isPull_unique hpo (hp _ _ r x₀)
    have e₁ : r ≫ x₀ = 1 := (Φ _).injective ((e₀.symm.trans (GtVec.isZero_unique ho₀ (hz _))))
    let k : TF (R := V) C ⟶ TE V C := Over.homMk (redE C) (by
      show redE C ≫ spMap (algebraMap C (DualNumber C)) ≫ (TF (R := V) C).hom = (TF (R := V) C).hom
      rw [← Category.assoc, GtVec.red_comp, Category.id_comp])
    let tf : TF (R := V) C ⟶ baseOver (Sp V) := Over.homMk (TF (R := V) C).hom (Category.comp_id _)
    have e₂ : k ≫ hh = tf ≫ r := by
      ext
      show redE C ≫ spMap (dualMap (toF V C)) = (TF (R := V) C).hom ≫ redE V
      rw [← hTF]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have e₃ : k ≫ hh ≫ x₀ = 1 := by
      rw [← Category.assoc, e₂, Category.assoc, e₁, MonObj.comp_one]
    have hpk := hp _ _ k (hh ≫ x₀)
    rw [e₃] at hpk
    let g := Φ (TF (R := V) C) 1
    refine ⟨⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩, ⟨(hz _).1, (hz _).2⟩, hpk⟩
  · intro hb
    have e := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ hh x₀)).1
    rw [e, hb]
    simp
  · intro a χ hval
    have hloc : IsLocalRing (DualNumber C) := TanLift.isLocalRing_dualNumber C
    have hlocH : IsLocalHom (TrivSqZeroExt.fstHom C C C).toRingHom :=
      ⟨fun x hx => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 hx⟩
    set gm := Φ _ (hh ≫ x₀)
    let J' : (Sp (DualNumber C) ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (redE C ≫ ψ)
    have hJ' : Good D.P.L (cpt (DualNumber C)) J' := fun ψ => by
      have h1 := ν.good (redE C ≫ ψ) (show cpt C ∈ (⊤ : (Sp C).Opens) from trivial)
      have hc : (redE C) (cpt C) = cpt (DualNumber C) :=
        IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom C C C).toRingHom
      have h2 : ψ ((redE C) (cpt C)) ∈ D.P.L.U (J' ψ) := h1
      rw [hc] at h2
      exact h2
    have ht := (top_le_iff_cpt (𝟙 (Sp (DualNumber C))) _).2 (hJ'.mem (DegPre.gtφT D (TE V C) gm.b χ) (𝟙 _))
    apply toStkA_injective (A := DualNumber C)
    have l1 := toStkA_valR (𝟙 (Sp (DualNumber C))) _ (cpt (DualNumber C)) ht ((gm.s χ).s _)
    have l2 := (val_corr hJ' ((hp _ _ hh x₀).2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    have l3 := hval _ (𝟙 _ ≫ hh.left) _ _ hJ'
    have hv1 : valR (𝟙 (Sp (DualNumber V))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom
        (1 + TrivSqZeroExt.inr a)) = 1 + TrivSqZeroExt.inr a := by
      have h0 : ⊤ ≤ 𝟙 (Sp (DualNumber V)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
      rw [valR, dif_pos h0]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [show (homOfLE h0) = 𝟙 (⊤ : (Sp (DualNumber V)).Opens) from rfl]
      simp
    have l4 := FormalValue.toStkA_map_valR (dualMap (toF V C)) (𝟙 (Sp (DualNumber V))) ⊤ (cpt (DualNumber C))
      (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))
    rw [hv1, Category.comp_id] at l4
    have hd : dualMap (toF V C) (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (toF V C a) := by
      ext <;> simp [dualMap]
    rw [hd] at l4
    rw [l4]
    refine l1.trans ?_
    refine (congrArg Units.val l2).trans ?_
    refine l3.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.MBLow.TanPull

end
