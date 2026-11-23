import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem memKL_mul_inv_of_eq (hL : L.IsLB) {Z : Over S} (x x' : Z ⟶ A)
    (h : ∀ (W : Over S) (a : W ⟶ A) (z : W ⟶ Z),
      CechPic.pull (a * (z ≫ x)).left (cls L hL) - CechPic.pull (z ≫ x).left (cls L hL) =
        CechPic.pull (a * (z ≫ x')).left (cls L hL) - CechPic.pull (z ≫ x').left (cls L hL)) :
    GlobalTheory.MemKL A L (x * x'⁻¹) := by
  intro p
  have hD : (Out.translDiff A L (x * x'⁻¹)).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL (x * x'⁻¹) hD (fst Z A) (snd Z A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have k₁ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x) = (fst Z A ≫ (x * x'⁻¹)) * snd Z A := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_comm _ (fst Z A ≫ x)]
    exact (_root_.mul_assoc _ _ _).symm
  have k₂ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x') = snd Z A := by
    rw [mul_comm, mul_inv_cancel_left]
  have e₃ := h (Z ⊗ A) ((fst Z A ≫ x')⁻¹ * snd Z A) (fst Z A)
  rw [k₁, k₂] at e₃
  have e₂ : cls _ hD = CechPic.pull (fst Z A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    exact sub_eq_sub_iff_sub_eq_sub.1 e₃
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst Z A).left ⁻¹ᵁ V).ι ≫ (fst Z A).left) (fun z ↦ z.2) hc

end

theorem inj_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  intro R _ _ A _ g hA _ L hL _ B P q hP _ hflat hsurj hev hKL
  haveI : IsCommMonObj A := hA.comm
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  intro Y u u' hs
  rw [same_iff hP.isLB hP.isLB] at hs
  let s₁ := pullback.snd q.left u.left
  let f₁ := pullback.fst q.left u.left
  let s₂ := pullback.snd q.left (s₁ ≫ u'.left)
  let f₂ := pullback.fst q.left (s₁ ≫ u'.left)
  let Z : Over (Sp R) := Over.mk (s₂ ≫ s₁ ≫ Y.hom)
  let c : Z ⟶ Y := Over.homMk (s₂ ≫ s₁) (by simp [Z])
  have w₁ : f₁ ≫ A.hom = s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Over.w u]
  have w₂ : f₂ ≫ A.hom = s₂ ≫ s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Category.assoc, Over.w u']
  let x : Z ⟶ A := Over.homMk (s₂ ≫ f₁) (by simp [Z, w₁])
  let x' : Z ⟶ A := Over.homMk f₂ (by simpa [Z] using w₂)
  have hx : c ≫ u = x ≫ q := by
    ext1
    simp only [Over.comp_left, c, x, Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hx' : c ≫ u' = x' ≫ q := by
    ext1
    simp only [Over.comp_left, c, x', Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hK : GlobalTheory.MemKL A L (x * x'⁻¹) := by
    refine memKL_mul_inv_of_eq hL x x' fun W a z ↦ ?_
    have e := congrArg (CechPic.pull (lift a (z ≫ c)).left) hs
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    simp only [Category.assoc] at e
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hev, hev] at e
    rw [← sub_eq_zero] at e ⊢
    convert e using 1
    abel
  have hq : x ≫ q = x' ≫ q := (hKL Z x x').2 hK
  have : Epi c.left := by
    have : Flat c.left := by simp only [c, Over.homMk_left]; infer_instance
    have : Surjective c.left := by simp only [c, Over.homMk_left]; infer_instance
    exact Flat.epi_of_flat_of_surjective _
  have : Epi c := Over.epi_of_epi_left c
  rw [← cancel_epi c, hx, hx', hq]

end GlobalTheory.DualCon
