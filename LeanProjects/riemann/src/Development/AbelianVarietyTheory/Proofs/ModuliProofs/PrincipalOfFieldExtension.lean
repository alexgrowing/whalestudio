import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SiegelDescent

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'}

private theorem hom_ext_tensor_left_of_fst_snd {B Z : Scheme.{0}} {X : Over B} (g k : Z ⟶ (X ⊗ X).left)
    (h1 : g ≫ (fst X X).left = k ≫ (fst X X).left) (h2 : g ≫ (snd X X).left = k ≫ (snd X X).left) : g = k := by
  have hw : k ≫ (X ⊗ X).hom = g ≫ (X ⊗ X).hom := by
    rw [← Over.w (fst X X), ← Category.assoc, ← h1, Category.assoc]
  have key := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ X).hom) ⟶ X ⊗ X)
    (Over.homMk k hw) (by ext; simpa using h1) (by ext; simpa using h2)
  exact congrArg CommaMorphism.left key

private theorem pGen_of_isGen_iso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : L'.Iso (L.pull F))
    (hw : w.IsGen) : PGen w := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨J, hJ⟩ : ∃ J : (L.pull F).ι, J = fun _ => j := ⟨_, rfl⟩
  obtain ⟨J', hJ'⟩ : ∃ J' : (L.pull F).ι, J' = fun _ => j' := ⟨_, rfl⟩
  have m1 : f y ∈ (L.pull F).U J := by rw [hJ]; exact mem_pull.2 hj
  have m2 : f y ∈ (L.pull F).U J' := by rw [hJ']; exact mem_pull.2 hj'
  have hy : f y ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
  have e := congrArg (gm f y _) (hw (J, k) (J', k'))
  rw [gm_res f y _ hy, map_mul, gm_res f y _ hy] at e
  have eg : gm f y (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k'))
      (((L.pull F).div L').g (J, k) (J', k')) =
      gm (f ≫ F) y (L.U j ⊓ L.U j') (L.g j j') * (gm f y (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ := by
    have hy' : f y ∈ (L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
    show gm f y ((L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k'))
      (res _ ((L.pull F).g J J') * (res _ (L'.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hy', gm_res f y _ hy', gm_pull_g L F f y J J' m1 m2]
    subst hJ hJ'
    rfl
  rw [eg] at e
  unfold gw
  subst hJ hJ'
  exact e

private theorem flat_spMap_of_field_hom' {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  unfold spMap
  infer_instance

private theorem surjective_spMap_of_field_hom {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  constructor
  intro x
  exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum K₀) _ _⟩

theorem lift_comp_square {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂)
    {T : Over S} {T' : Over S'} (u : T'.left ⟶ T.left) (a b : T ⟶ A) (a' b' : T' ⟶ A')
    (ha : a'.left ≫ φ = u ≫ a.left) (hb : b'.left ≫ φ = u ≫ b.left) :
    (lift a' b').left ≫ φ₂ = u ≫ (lift a b).left := by
  have e1 : (lift a' b').left ≫ (fst A' A').left = a'.left := by rw [← Over.comp_left, lift_fst]
  have e2 : (lift a b).left ≫ (fst A A).left = a.left := by rw [← Over.comp_left, lift_fst]
  have e3 : (lift a' b').left ≫ (snd A' A').left = b'.left := by rw [← Over.comp_left, lift_snd]
  have e4 : (lift a b).left ≫ (snd A A).left = b.left := by rw [← Over.comp_left, lift_snd]
  apply hom_ext_tensor_left_of_fst_snd
  · rw [Category.assoc, hs.1, ← Category.assoc, e1, ha, Category.assoc, e2]
  · rw [Category.assoc, hs.2, ← Category.assoc, e3, hb, Category.assoc, e4]

theorem eq_one_of_pull {f : S' ⟶ S} [Flat f] [Surjective f] [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (h : IsGrpPullback A' A f φ) (hs : IsSquare φ φ₂) (hP : P.IsLB) (hP' : P'.IsLB) (hw : LBIso P' (P.pull φ₂))
    (hK : ∀ (T : Over S') (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t, ht⟩ := hx
  let T' : Over S' := Over.mk (pullback.snd T.hom f)
  let p : T'.left ⟶ T.left := pullback.fst T.hom f
  have hp : p ≫ T.hom = T'.hom ≫ f := pullback.condition
  have hxl : (p ≫ x.left) ≫ A.hom = T'.hom ≫ f := by rw [Category.assoc, Over.w x]; exact hp
  let xl : T'.left ⟶ A'.left := h.1.lift (p ≫ x.left) T'.hom hxl
  have hxl1 : xl ≫ φ = p ≫ x.left := h.1.lift_fst _ _ _
  have hxl2 : xl ≫ A'.hom = T'.hom := h.1.lift_snd _ _ _
  let x' : T' ⟶ A' := Over.homMk xl hxl2
  have hA : φ ≫ A.hom = A'.hom ≫ f := h.1.w
  let Z : Over S := Over.mk ((A' ⊗ T').hom ≫ f)
  let a0 : Z ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    rw [Category.assoc, hA, ← Category.assoc, Over.w (fst A' T')]; rfl)
  let b0 : Z ⟶ T := Over.homMk ((snd A' T').left ≫ p) (by
    rw [Category.assoc, hp, ← Category.assoc, Over.w (snd A' T')]; rfl)
  let q : (A' ⊗ T').left ⟶ (A ⊗ T).left := (lift a0 b0).left
  have hq1 : q ≫ (fst A T).left = (fst A' T').left ≫ φ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hq2 : q ≫ (snd A T).left = (snd A' T').left ≫ p := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hc : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ = q ≫ (lift (snd A T ≫ x) (fst A T)).left := by
    refine lift_comp_square hs q _ _ _ _ ?_ hq1.symm
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc q, hq2, Category.assoc]
    exact congrArg ((snd A' T').left ≫ ·) hxl1
  obtain ⟨a, ha, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move hP hP' w (pGen_of_isGen_iso_pull w hwg) (K := PUnit)
    (fun _ => (lift (snd A T ≫ x) (fst A T)).left) (fun _ => (lift (snd A' T' ≫ x') (fst A' T')).left)
    (fun _ => 1) q (fun _ => hc) t ht
  have hx' : x' = 1 := hK T' x' ⟨a, ha⟩
  let Zp : Over S := Over.mk (T'.hom ≫ f)
  let z : Zp ⟶ A := Over.homMk (p ≫ x.left) hxl
  have hz : z.left = (1 : T' ⟶ A').left ≫ φ := by
    show p ≫ x.left = _
    rw [← hxl1, ← hx']
    rfl
  have hzz := h.2 T' 1 1 z z hz hz
  rw [_root_.mul_one] at hzz
  have hz1 : z = 1 := by
    have e : z * z = z * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext (hzz.trans hz.symm)
    exact mul_left_cancel e
  have hfl : Flat p := inferInstanceAs (Flat (pullback.fst T.hom f))
  have hsu : Surjective p := inferInstanceAs (Surjective (pullback.fst T.hom f))
  have hpe : Epi p := Flat.epi_of_flat_of_surjective p
  let pO : Zp ⟶ T := Over.homMk p hp
  have e1 : pO ≫ x = z := Over.OverMorphism.ext rfl
  have e2 : pO ≫ (1 : T ⟶ A) = 1 := by
    simp
  have hfin : p ≫ x.left = p ≫ (1 : T ⟶ A).left := by
    have e3 := congrArg CommaMorphism.left ((e1.trans hz1).trans e2.symm)
    exact e3
  exact Over.OverMorphism.ext ((cancel_epi p).1 hfin)

theorem principal_of_fieldExtension : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c₀ : SiegPre h M ζ s₀) (c : SiegPre h M ζ s), SiegPB c c₀ (spMap i) → c.Principal → c₀.Principal := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c₀ c hpb hc
  obtain ⟨φ, φ₂, hg, hs, hw, -⟩ := hpb
  have hfl : Flat (spMap i) := flat_spMap_of_field_hom' i
  have hsu : Surjective (spMap i) := surjective_spMap_of_field_hom i
  refine ⟨?_, fun T x hx => eq_one_of_pull hg hs c₀.isLB c.isLB hw hc.2 T x hx⟩
  obtain ⟨w, hwg⟩ := hw
  have hΔ : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left :=
    lift_comp_square hs φ _ _ _ _ (by simp) (by simp)
  have i1 : LBIso c.diag (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) := by
    have := iso_linComb (pGen_of_isGen_iso_pull w hwg) (K := PUnit) (fun _ => (lift (𝟙 c.A) (𝟙 c.A)).left) (fun _ => 1)
    rw [hΔ] at this
    exact this
  obtain ⟨w₀, hw₀⟩ := exists_iso_linComb c₀.isLB (K := PUnit) (F := (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)
    (fun _ => (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (fun _ => 1) (fun _ _ _ => rfl)
  have i2 : LBIso (c₀.diag.pull φ) (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) :=
    iso_linComb (pGen_of_isGen_iso_pull w₀ hw₀) (K := PUnit) (fun _ => φ) (fun _ => 1)
  have hd : LBIso c.diag (c₀.diag.pull φ) :=
    LBIso.trans (pull_isLB c.isLB _) (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c₀.isLB _) _) i1 i2.symm
  exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i c₀.A c.A φ c₀.diag c.diag c₀.ab hg
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) hd hc.1

end GlobalTheory.SiegelDescent
