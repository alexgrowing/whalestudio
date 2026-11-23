import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.PolLift
open GlobalTheory.AbDual GlobalTheory.CechPic

theorem lbIso_symm {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : LBIso Q P :=
  (cls_eq_iff hQ hP).1 ((cls_eq_iff hP hQ).2 e).symm

theorem gen_comp {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : (P.pull (g ≫ f)).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff (pull_isLB hP _)).2 h, map_zero]

theorem gen_pull_pull {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (a : Y ⟶ X) (x : Z ⟶ Y)
    (h : ∃ t : (P.pull (x ≫ a)).Gen, t.IsGen) : ∃ t : ((P.pull a).pull x).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [cls_pull (pull_isLB hP _), cls_pull hP, ← pull_comp, ← cls_pull hP _ (pull_isLB hP _)]
  exact (cls_eq_zero_iff (pull_isLB hP _)).2 h

theorem gen_left {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB) (u : A ⟶ A) [IsMonHom u]
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) :
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) := by
  refine ⟨gen_pull_pull hP _ _ ?_, gen_pull_pull hP _ _ ?_⟩
  · rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, MonObj.one_comp]
    exact h₁
  · have e : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ u) (snd A A) = u ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, lift_fst_assoc, lift_snd, comp_lift, Category.id_comp, Category.comp_id, MonObj.comp_one]
    rw [← Over.comp_left, e, Over.comp_left]
    exact gen_comp hP _ _ h₂

theorem sq_left {S S' : Scheme.{0}} {A₀ : Over S'} {A : Over S} [GrpObj A₀] [GrpObj A] {i : A₀.left ⟶ A.left}
    {l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left} (l₁ : l ≫ (fst A A).left = (fst A₀ A₀).left ≫ i)
    (l₂ : l ≫ (snd A A).left = (snd A₀ A₀).left ≫ i) (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) (w : u₀.left ≫ i = i ≫ u.left) :
    (lift (fst A₀ A₀ ≫ u₀) (snd A₀ A₀)).left ≫ l = l ≫ (lift (fst A A ≫ u) (snd A A)).left := by
  apply GlobalTheory.AbDual.left_ext
  · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst,
      Over.comp_left, Over.comp_left, Category.assoc, w, ← Category.assoc, ← l₁, Category.assoc]
  · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd, l₂]

theorem exists_pol_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) h, ∀ y ∈ liftFil (divided₂ hsq) h, φ x y = 0) → ∃ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)) ∧ IsSquare i φ₂ ∧ LBIso o₀.P (P.pull φ₂) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hiso
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A hA
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  have hsq2 : Geo.Tor.IsSquare i l := ⟨l₁, l₂⟩
  have C' := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA hg hA hg h h
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C' o₀.isLB o₀.rig₁ o₀.rig₂
  have hΔ₀ : (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left).IsLB := pull_isLB o₀.isLB _
  obtain ⟨P, hP, t₁, t₂, -, -, eP⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hg hA hg h h l₁ l₂
    hΔ₀ o₀.ample hΔ₀ o₀.ample o₀.isLB o₀.rig₁ o₀.rig₂ hφ₀ (hiso φ₀ hφ₀)
  have wΔ : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ l = i ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have aL : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    haveI := hA.smooth
    exact GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening C C₀ (RingHom.ker π) κ hκ π hπ rfl A o₀.A i h.1 inferInstance _ _
      hL hΔ₀ (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ i wΔ) o₀.ample
  have symm := GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2
    _ hL aL o₀.P o₀.isLB o₀.symm P hP t₁ t₂ eP
  have ros : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
      (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left) := by
    intro c
    haveI := o₀.act.hom c
    haveI := act.hom c
    haveI := o₀.act.hom (D.star c).unop
    haveI := act.hom (D.star c).unop
    have hQ := pull_isLB hP (lift (fst A A ≫ act.act c) (snd A A)).left
    have hQ₀ := pull_isLB o₀.isLB (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left
    obtain ⟨q₁, q₂⟩ := gen_left P hP (act.act c) t₁ t₂
    have eQ : LBIso ((P.pull (lift (fst A A ≫ act.act c) (snd A A)).left).pull l)
        (o₀.P.pull (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left) :=
      lbIso_symm hQ₀ (pull_isLB hQ _) (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ l
        (sq_left l₁ l₂ _ _ (hact c)))
    exact GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2 _ hL aL
      (o₀.act.act (D.star c).unop) (act.act (D.star c).unop) (hact _) o₀.P _ o₀.isLB hQ₀ (o₀.rosati c)
      P _ hP hQ t₁ t₂ q₁ q₂ eP eQ
  have ker : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, H⟩ := o₀.kerP
    have hu : IsUnit (e : C) := by
      have := (b.unit e he).map tR
      simpa using this
    exact ⟨e, he, GlobalTheory.T.lifted_polarisation_kernel_killed_of_unit C C₀ π hπ hsq o₀.A A i h hA l hsq2 o₀.P P o₀.isLB hP t₁ t₂ symm aL eP e hu H⟩
  exact ⟨P, l, hP, t₁, t₂, symm, aL, ker, ros, hsq2, lbIso_symm (pull_isLB hP l) o₀.isLB eP⟩

end GlobalTheory.UPel.HT.PolLift
