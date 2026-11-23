import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleProd

open GlobalTheory.CechPic

section Local

variable {Y Y' B B' : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ pull (π ⁻¹ᵁ V).ι c = 0

theorem pull_eq_zero_of_range {W : Y.Opens} {c : Pic Y} (H : pull W.ι c = 0) (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) :
    pull h c = 0 := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW y
  rw [← IsOpenImmersion.lift_fac W.ι h hr, pull_comp, H, map_zero]

theorem LocZero.sub {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) : LocZero π (c - d) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  rw [map_sub, pull_eq_zero_of_range t (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.1,
    pull_eq_zero_of_range t' (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.2, sub_zero]

theorem LocZero.pull_over {π : Y ⟶ B} {c : Pic Y} (H : LocZero π c) {π' : Y' ⟶ B} (h : Y' ⟶ Y) (sq : h ≫ π = π') :
    LocZero π' (pull h c) := by
  subst sq
  intro p
  obtain ⟨V, hV, t⟩ := H p
  refine ⟨V, hV, ?_⟩
  rw [← pull_comp]
  exact pull_eq_zero_of_range t _ fun y => y.2

theorem locZero_base (π : Y ⟶ B) (c : Pic B) : LocZero π (pull π c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL p
  refine ⟨L.U i, hi, ?_⟩
  rw [← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hL _)).2
    (BoxKernel.gen_of_chart (pull_isLB hL _) (fun _ => i) fun y => mem_pull.2 y.2)

theorem locZero_iff (π : Y ⟶ B) {N : LB Y} (hN : N.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (N.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls N hN) :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (cls_eq_zero_iff (pull_isLB hN _)).symm

end Local

section Kernel

variable {S : Scheme.{0}} {A G H : Over S} [GrpObj A] [GrpObj G] [GrpObj H]

theorem cls_translDiff {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _) =
      pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
  refine (cls_linComb hL _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  show (1 : ℤ) • pull ((fst T A ≫ x) * snd T A).left (cls L hL) + (-1 : ℤ) • pull (snd T A).left (cls L hL) = _
  rw [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

theorem locZero_translDiff_comp {N : LB A.left} {L : LB G.left} (hN : N.IsLB) (hL : L.IsLB) (b : Pic H.left)
    (p : A ⟶ G) (q : A ⟶ H) [IsMonHom p] [IsMonHom q] (u : G ⟶ A) (hp : u ≫ p = 𝟙 G) (hq : u ≫ q = 1)
    (e : cls N hN = pull p.left (cls L hL) + pull q.left b) {T : Over S} (x : T ⟶ A)
    (hx : LocZero (fst T A).left (cls (Out.translDiff A N x) (LB.isLB_linComb hN _ _))) :
    LocZero (fst T G).left (cls (Out.translDiff G L (x ≫ p)) (LB.isLB_linComb hL _ _)) := by
  have H₁ := hx.pull_over (π' := (fst T G).left) (T ◁ u).left (congrArg (fun q => q.left) (whiskerLeft_fst T u))
  have H₂ := (H₁.sub (locZero_base (fst T G).left (pull (x ≫ q).left b))).sub
    (locZero_base (fst T G).left (-pull (1 : T ⟶ H).left b))
  have e₁ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ p = (fst T G ≫ x ≫ p) * snd T G := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hp,
      Category.comp_id]
  have e₂ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ q = fst T G ≫ x ≫ q := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hq,
      MonObj.comp_one, _root_.mul_one]
  have e₃ : T ◁ u ≫ snd T A ≫ p = snd T G := by rw [whiskerLeft_snd_assoc, hp, Category.comp_id]
  have e₄ : T ◁ u ≫ snd T A ≫ q = fst T G ≫ (1 : T ⟶ H) := by
    rw [whiskerLeft_snd_assoc, hq, MonObj.comp_one, MonObj.comp_one]
  convert H₂ using 1
  rw [cls_translDiff hL, cls_translDiff hN, e]
  simp only [map_sub, map_add, map_neg, ← pull_comp, ← Over.comp_left, e₁, e₂, e₃, e₄]
  abel

theorem kTriv_prod {N : LB (G ⊗ H).left} {L : LB G.left} {L' : LB H.left} (hN : N.IsLB) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : cls N hN = pull (fst G H).left (cls L hL) + pull (snd G H).left (cls L' hL'))
    (hK : Out.KTriv G L) (hK' : Out.KTriv H L') : Out.KTriv (G ⊗ H) N := by
  intro R _ t x hx
  have hx' := (locZero_iff _ (LB.isLB_linComb hN _ _)).1 hx
  have h₁ : x ≫ fst G H = 1 := hK R t _ ((locZero_iff _ (LB.isLB_linComb hL _ _)).2
    (locZero_translDiff_comp hN hL _ (fst G H) (snd G H) (lift (𝟙 G) 1) (lift_fst _ _) (lift_snd _ _) e x hx'))
  have h₂ : x ≫ snd G H = 1 := hK' R t _ ((locZero_iff _ (LB.isLB_linComb hL' _ _)).2
    (locZero_translDiff_comp hN hL' _ (snd G H) (fst G H) (lift 1 (𝟙 H)) (lift_snd _ _) (lift_fst _ _)
      (e.trans (add_comm _ _)) x hx'))
  show x = 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [h₁, MonObj.one_comp]
  · rw [h₂, MonObj.one_comp]

end Kernel

section Cube

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] {n : ℕ}

def cubeCls {T : Over S} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem cubeCls_add {T : Over S} (x : Fin n → (T ⟶ G)) (c d : Pic G.left) :
    cubeCls x (c + d) = cubeCls x c + cubeCls x d := by
  simp only [cubeCls, map_add, smul_add, Finset.sum_add_distrib]

theorem pull_cubeCls {T T' : Over S} (ρ : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left)
    (y : Fin n → (T' ⟶ G)) (h : ∀ i, y i = ρ ≫ x i) : cubeCls y c = pull ρ.left (cubeCls x c) := by
  rw [cubeCls, cubeCls, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, PrimNorm.psum_pre ρ x y h]

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) {T : Over S}

abbrev ppCls : Pic t.G.left := cls t.PP.L t.PP.isLB

end Triple

end GlobalTheory.TripleProd
