import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveAlgebraisationFormalEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemPowOfFlatQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Algebraise
variable {X Y : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (rs_rs h₁ h₂ u.val)

theorem pw_pw (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem pw_pull (H : LB X) (f : Y ⟶ X) (a : ℤ) :
    (AbLaw.pw H a).pull f = AbLaw.pw (H.pull f) a := by
  have : ((AbLaw.pw H a).pull f).g = (AbLaw.pw (H.pull f) a).g := by
    funext j j'
    change (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k) ^ a))) ^ (1 : ℤ)) =
      (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k)))) ^ (1 : ℤ)) ^ a
    simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact congrArg (fun g => (⟨(H.pull f).ι, (H.pull f).U, g⟩ : LB Y)) this

theorem lbIso_pw {A B : LB X} (h : LBIso A B) (a : ℤ) : LBIso (AbLaw.pw A a) (AbLaw.pw B a) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => (w.s p) ^ a⟩, fun p q => ?_⟩
  have key : ∀ {G : Type} [CommGroup G] {x y z u : G}, x = y * z⁻¹ * u →
      x ^ a = y ^ a * (z ^ a)⁻¹ * u ^ a := by
    rintro G _ x y z u rfl
    rw [mul_zpow, mul_zpow, inv_zpow]
  change res _ (w.s p ^ a) = (res _ (B.g p.1 q.1 ^ a) * (res _ (A.g p.2 q.2 ^ a))⁻¹) * res _ (w.s q ^ a)
  rw [map_zpow, map_zpow, map_zpow, map_zpow]
  exact key (hw p q)

theorem cocycle_on {H : LB X} (hH : H.IsLB) (i j k : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hj : W ≤ H.U j) (hk : W ≤ H.U k) :
    res (le_inf hi hj) (H.g i j) * res (le_inf hj hk) (H.g j k) = res (le_inf hi hk) (H.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk : W ≤ H.U i ⊓ H.U j ⊓ H.U k)) (hH.cocycle i j k)
  simpa only [map_mul, res_res] using h

theorem rel_on {H : LB X} (hH : H.IsLB) (i k i' k' : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hk : W ≤ H.U k) (hi' : W ≤ H.U i') (hk' : W ≤ H.U k') :
    res (le_inf hi hk) (H.g i k) = res (le_inf hi hi') (H.g i i') * (res (le_inf hk hk') (H.g k k'))⁻¹ *
      res (le_inf hi' hk') (H.g i' k') := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocycle_on hH i k k' hi hk hk',
    cocycle_on hH i i' k' hi hi' hk']

theorem lbIso_tw {H : LB X} (hH : H.IsLB) (t : ℤ) : LBIso (AbLaw.pw H (t + 1)) (tw H H t) := by
  refine ⟨⟨fun p => res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.1 ⊓ H.U p.2) (H.g p.1.1 p.2) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.2 ⊓ H.U p.2) (H.g p.1.2 p.2) ^ t⟩, ?_⟩
  rintro ⟨⟨i, j : H.ι⟩, k : H.ι⟩ ⟨⟨i', j' : H.ι⟩, k' : H.ι⟩
  let W : X.Opens := H.U i ⊓ H.U j ⊓ H.U k ⊓ (H.U i' ⊓ H.U j' ⊓ H.U k')
  have hi : W ≤ H.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : W ≤ H.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hk : W ≤ H.U k := inf_le_left.trans inf_le_right
  have hi' : W ≤ H.U i' := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hj' : W ≤ H.U j' := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hk' : W ≤ H.U k' := inf_le_right.trans inf_le_right
  change res (inf_le_left : W ≤ H.U i ⊓ H.U j ⊓ H.U k) (res _ (H.g i k) * res _ (H.g j k) ^ t) =
    (res (V := W) (U := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _
        (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g i i') *
          (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g j j' ^ (-t)))⁻¹) *
      (res (V := W) _ (H.g k k' ^ (t + 1)))⁻¹) *
    res (inf_le_right : W ≤ H.U i' ⊓ H.U j' ⊓ H.U k') (res _ (H.g i' k') * res _ (H.g j' k') ^ t)
  simp only [map_mul, map_inv, map_zpow, res_res]
  erw [res_res, res_res]
  rw [rel_on hH i k i' k' hi hk hi' hk', rel_on hH j k j' k' hj hk hj' hk']
  simp only [zpow_neg, inv_inv, mul_zpow, inv_zpow, zpow_add_one, mul_inv]
  ac_rfl

theorem exists_veryAmple_h1Zero (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) (L : LB B.left) (hL : L.IsLB) (h : RelAmple B L) :
    ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes (AbLaw.pw L d) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy B.hom (AbLaw.pw L d) s := by
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 R B.left B.hom _ n₀ s₀ hH hs₀ _ hH
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw h1
  have h3 := veryAmpleBy_pw R B.left B.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

theorem algebraisation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (M H : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left) (n d : ℕ) (s : Fin (n + 1) → LB.Sec H), M.IsLB ∧ H.IsLB ∧ Flat B.hom ∧ VeryAmpleBy B.hom H s ∧ 1 ≤ d ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) ∧ LBIso (pw (N e) d) (H.pull (b e)) := by
  intro V _ _ _ _ Y β hβ hY N v hN hA
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := exists_veryAmple_h1Zero _ (Y 0) (N 0) (hN 0).1 hA
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [pw_pull]
    exact lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, hw, -⟩ := GlobalTheory.Unif.exists_projective_of_formal_embedding V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have := isProper_of_isProjBy V B.left B.hom hP
  have hF : Flat B.hom := GlobalTheory.FlatThickenings.flat_of_flat_thickenings V B Y b hb hY
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hP hF hb hbβ N v hN
  exact ⟨B, M, H, b, n, d, s', hM, hH, hF, hB, hd, hb, hbβ, fun e => ⟨hNM e, w e, (hw e).1⟩⟩

end GlobalTheory.Algebraise
