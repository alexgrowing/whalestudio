import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SymRoot

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def rigCls (c : Pic A.left) : Pic A.left := c - pull (1 : A ⟶ A).left c

theorem pull_rigCls (c : Pic A.left) (x : T ⟶ A) :
    pull x.left (rigCls c) = pull x.left c - pull (1 : T ⟶ A).left c := by
  rw [rigCls, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_one]

theorem lam_rigCls (c : Pic A.left) (x y : T ⟶ A) : lam (rigCls c) x y = lam c x y := by
  simp only [lam, pull_rigCls]
  abel

theorem lam_diag [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hs : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) :
    lam (cls L hL) (𝟙 A) (𝟙 A) = 2 • rigCls (cls L hL) := by
  have h := lam_mul_left hL hΘ (𝟙 A) (𝟙 A)⁻¹ (𝟙 A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls L hL) (𝟙 A)⁻¹ (𝟙 A) = -(2 • rigCls (cls L hL)) := by
    rw [lam, inv_mul_cancel, Hom.inv_def, Category.id_comp, hs, Over.id_left, pull_id, rigCls]
    abel
  rw [e] at h
  exact add_neg_eq_zero.1 h.symm

theorem exists_polAV_sqOf : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  intro laws h k o _ ζ R _ _ β c L ⟨ha, hk⟩ hdim hL hΛ hs
  have hA := c.ab
  have hd : c.diag.IsLB := pull_isLB c.isLB _
  have hp : IsProjBy c.A.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ c.A c.diag hA hd ha R (𝟙 _) _ (𝟙 _) c.A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ : ∃ t : LB.Gen (Theta c.A L), t.IsGen := CubeAffine.triv_theta_of_isProjBy laws R c.A hA hp L hL
  have s₁ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls L hL) = cls L hL :=
    ((cls_eq_iff hL (pull_isLB hL _)).2 hs).symm
  have e₀ : cls c.P c.isLB = lam (cls L hL) (fst c.A c.A) (snd c.A c.A) :=
    ((cls_eq_iff (LB.isLB_linComb hL _ _) c.isLB).2 hΛ).symm.trans (cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  obtain ⟨M, hM, e⟩ := cls_surj (rigCls (cls L hL))
  have e₁ : cls c.P c.isLB = lam (cls M hM) (fst c.A c.A) (snd c.A c.A) := by rw [e, lam_rigCls, e₀]
  have e₂ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls M hM) = cls M hM := by
    rw [e, pull_rigCls, s₁, rigCls]
  have e₃ : cls c.diag hd = 2 • cls M hM := by
    refine (cls_pull c.isLB _ _).trans ?_
    rw [e₀, pull_lam, lift_fst, lift_snd, lam_diag hL hΘ s₁, e]
  have hr : Out.Rigidified c.A M := by
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ((cls_pull hM _ _).trans ?_)
    have e₄ : (η[c.A] : 𝟙_ _ ⟶ c.A) = 1 := by rw [Hom.one_def]; simp
    have := pull_rigCls (cls L hL) η[c.A]
    rw [← e₄, sub_self, ← e] at this
    exact this
  have hsym : Out.Sym c.A M := fun s => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]⟩
  have hamp : Out.RelAmple c.A M := by
    have f : IsFinite (𝟙 c.A : c.A ⟶ c.A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ c.A c.A (𝟙 _) M 2 two_pos hA hA hM f).2.1.1
      ((relAmple_finite_pow_iso _ c.A c.A (𝟙 _) _ 2 two_pos hA hA hd f).2.2.2 _ (isLB_lbPow hM 2) ?_ ha)
    exact (cls_eq_iff hd (isLB_lbPow hM 2)).1 (e₃.trans (cls_lbPow hM 2 _).symm)
  have hid : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  refine ⟨{ A := c.A, isAb := hA, g := h, smoothDim := hdim, L := M, isLB := hM, rigid := hr, sym := hsym,
            ample := hamp, ktriv := ThetaExtend.kTriv_of_lam hM c.isLB e₁ hk }, 𝟙 _,
    (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl, rfl, 𝟙 _, ⟨by simp, by simp⟩, ?_⟩
  refine (cls_eq_iff (LB.isLB_linComb hM _ _) (pull_isLB c.isLB _)).1 ?_
  exact (cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans (e₁.symm.trans (pull_id _).symm)

end GlobalTheory.SymRoot
