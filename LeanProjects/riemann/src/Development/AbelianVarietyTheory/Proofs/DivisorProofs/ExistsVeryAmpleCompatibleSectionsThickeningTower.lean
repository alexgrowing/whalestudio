import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformLiftSectionsThickeningTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConsecutiveVeryAmplePowersRelAmpleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.TowerVA

theorem exists_compatible_of_lift (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB) (p k c : ℕ) (hk : 1 ≤ k) (hc : (c : ℤ) = (p : ℤ) * (k : ℤ))
    (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) p))
    (hs : VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) p) s)
    (hlift : ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))),
      (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) →
        ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e))
    (v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e))) (hv : ∀ e, (v e).IsGen) :
    ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)),
      (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  have hEq : GlobalTheory.AbLaw.pw (N 0) c = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k := by
    rw [hc]
    exact congrArg (fun g => (⟨(N 0).ι, (N 0).U, g⟩ : LB (Y 0).left))
      (funext fun i => funext fun j => zpow_mul ((N 0).g i j) _ _)
  have h0 : ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) c)),
      VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) c) s' := by
    rw [hEq]
    exact GlobalTheory.AbLaw.veryAmpleBy_pw _ _ _ _ n s (isLB_pw (hN 0) _) hs k hk
  obtain ⟨n', s0, hs0⟩ := h0
  have hL : ∀ e, (GlobalTheory.AbLaw.pw (N e) c).IsLB ∧ (v e).IsGen := fun e => ⟨isLB_pw (hN e) _, hv e⟩
  have hiso : LBIso (GlobalTheory.AbLaw.pw (N 0) c) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) :=
    hEq ▸ lbIso_refl (isLB_pw (hN 0) _)
  choose σ hσ0 hσ using fun j => hlift (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL hiso (s0 j)
  refine ⟨n', fun e j => σ j e, fun e j => hσ j e, ?_⟩
  rintro (_ | e)
  · show VeryAmpleBy _ _ (fun j => σ j 0)
    simp only [hσ0]
    exact hs0
  · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL (fun e j => σ j e)
      (fun e j => hσ j e) e
    simp only [hσ0] at hr
    exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
      (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w n' _ _ (hL _).1 (hL _).1
      ((isGen_iff _).2 hw) hr hs0

theorem exists_veryAmple_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  intro R _ _ I Y β hβ N hN hamp
  obtain ⟨d, hd1, hd⟩ := GlobalTheory.T.exists_consecutive_veryAmple_powers_relAmple (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0) hamp
  obtain ⟨n₁, s₁, hs₁⟩ := hd d (Or.inl rfl)
  obtain ⟨n₂, s₂, hs₂⟩ := hd (d + 1) (Or.inr rfl)
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₁ s₁ (isLB_pw (hN 0) _) hs₁
  obtain ⟨k₂, hk₂⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₂ s₂ (isLB_pw (hN 0) _) hs₂
  refine ⟨d * (1 + (d + 1) * max k₁ k₂), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have ht1 : ∀ m t : ℕ, 1 ≤ m → t ≤ 1 + m * t := fun m t hm => by nlinarith
  rintro c (rfl | rfl) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN d (1 + (d + 1) * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₁ s₁ hs₁ (hk₁ _ (le_trans (le_max_left _ _) (ht1 _ _ (by omega)))) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN (d + 1) (1 + d * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₂ s₂ hs₂ (hk₂ _ (le_trans (le_max_right _ _) (ht1 _ _ hd1))) v hv

end GlobalTheory.FormalAlg.TowerVA
