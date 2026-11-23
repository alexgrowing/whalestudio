import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinsetStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.RigSymSubring

open GlobalTheory.CechPic

theorem pic_descends (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S)
    (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (c d : Pic X₀)
    (H : IsPullback π f f₀ (spMap R₀.subtype)) (e : pull π c = pull π d) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀),
        IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → pull π₁ c = pull π₁ d := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨F, hF⟩ := GlobalTheory.T.lineBundleIso_descends_to_subring_of_finset S R₀ X X₀ f f₀ π M N H hM hN
    ((cls_eq_iff (pull_isLB hM π) (pull_isLB hN π)).1 e)
  exact ⟨F, fun R₁ h hR X₁ f₁ π₁ H₁ =>
    (cls_eq_iff (pull_isLB hM π₁) (pull_isLB hN π₁)).2 (hF R₁ h hR X₁ f₁ π₁ H₁)⟩

variable {T : Scheme.{0}} {A : Over T} [GrpObj A] {L : LB A.left}

theorem rigidified_iff (hL : L.IsLB) : Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem gen_iff (hL : L.IsLB) {Y : Scheme.{0}} (r : Y ⟶ A.left) :
    (∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![r ≫ (GrpObj.inv : A ⟶ A).left, r] ![1, -1]), t.IsGen) ↔
      pull r (pull (GrpObj.inv : A ⟶ A).left (cls L hL)) = pull r (cls L hL) := by
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two, ← pull_comp]
  simp [← sub_eq_add_neg, sub_eq_zero]

theorem sym_of_cls (hL : L.IsLB) (e : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) : Out.Sym A L :=
  fun _ => ⟨⊤, trivial, (gen_iff hL _).2 (by rw [e])⟩

theorem cls_of_sym {S : Type} [CommRing S] [IsLocalRing S] {A : Over (Sp S)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, ht⟩ := hs (IsLocalRing.closedPoint S)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have i : ∀ c : Pic A.left, pull (inv (A.hom ⁻¹ᵁ ⊤).ι (I := inferInstanceAs (IsIso A.left.topIso.hom)))
      (pull (A.hom ⁻¹ᵁ ⊤).ι c) = c := fun c => by rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  exact (i _).symm.trans ((congrArg _ ((gen_iff hL _).1 ht)).trans (i _))

end GlobalTheory.RigSymSubring

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.RigSymSubring

theorem rigidified_sym_descend_to_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.Rigidified A₁ (L₀.pull π) ∧ Out.Sym A₁ (L₀.pull π) := by
  classical
  intro S _ _ R₀ P A₀ _ φ L₀ hA hL H hw
  have := hA.proper
  have hc : cls P.L P.isLB = pull φ (cls L₀ hL) := (cls_eq_iff P.isLB (pull_isLB hL φ)).2 hw
  have e₁ : pull (spMap R₀.subtype) (pull (X := A₀.left) (Y := Sp R₀) (eSec A₀) (cls L₀ hL)) =
      pull (spMap R₀.subtype) 0 := by
    have h₁ := (rigidified_iff P.isLB).1 P.rigid
    rw [hc, ← pull_comp, PolBaseChange.eSec_comm H] at h₁
    exact (pull_comp _ _ _).symm.trans (h₁.trans (map_zero _).symm)
  have e₂ : pull φ (pull (GrpObj.inv : A₀ ⟶ A₀).left (cls L₀ hL)) = pull φ (cls L₀ hL) := by
    have h₂ := cls_of_sym P.isLB P.sym
    rwa [hc, ← pull_comp, PolBaseChange.inv_comm H, pull_comp] at h₂
  obtain ⟨F₁, h₁⟩ := pic_descends S R₀ (Sp S) (Sp R₀) (𝟙 _) (𝟙 _) (spMap R₀.subtype) _ _
    (IsPullback.of_vert_isIso ⟨by simp⟩) e₁
  obtain ⟨F₂, h₂⟩ := pic_descends S R₀ _ _ P.A.hom A₀.hom φ _ _ H.1 e₂
  refine ⟨F₁ ∪ F₂, fun R₁ h hF A₁ _ π H₁ => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  have a := h₁ R₁ h hF.1 (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h)) (IsPullback.of_vert_isIso ⟨by simp⟩)
  have b := h₂ R₁ h hF.2 _ A₁.hom π H₁.1
  refine ⟨(rigidified_iff (pull_isLB hL π)).2 ?_, sym_of_cls (pull_isLB hL π) ?_⟩
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.eSec_comm H₁]
    exact (pull_comp _ _ _).trans (a.trans (map_zero _))
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.inv_comm H₁, pull_comp, b]

end GlobalTheory
