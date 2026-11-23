import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem colRho : StatColRho := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' tens v₁ κ
    htens he₁ hK hE hk0 hδ φ l
  obtain ⟨-, hσ, -, h4⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  choose x hx using fun a => he₁ _ (hσ a)
  have key : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) +
      (uElt r χ g • φ (nuGen r χ E e₁ δ D j Kc k0 l) - φ (nuGen r χ E e₁ δ D j Kc k0 l)) =
      (δO * (ℓ : O) ^ e' l) • ∑ a, tens (κ l a g) (x a) := by
    intro g hg
    rw [h4 g hg]
    obtain ⟨b, hb⟩ := hk0 l g
    rw [hb, mul_smul, hE, smul_zero, add_zero, hδ, mul_smul, Finset.smul_sum (r := (ℓ : O) ^ e' l)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK l a g hg, map_smul, LinearMap.smul_apply]
  refine ⟨⟨x, key⟩, fun F hF => ?_⟩
  set ρM := uRep O (M := M) r χ with hρM
  set Ψφ := colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ with hΨ
  have hz := hF (restrictCocycles1 ρM (D l) Ψφ + cobZ (resRep ρM (D l)) (φ (nuGen r χ E e₁ δ D j Kc k0 l)))
    (fun a => (δO * (ℓ : O) ^ e' l) • x a) (fun g => by
      have := key g g.2
      simp only [map_smul, ← Finset.smul_sum]
      exact this)
  rw [map_add, mkQ_cobZ, add_zero] at hz
  exact hz

theorem liftBound : StatLiftBound := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ e₁ Dl j Kc ℓ e' tens v₁ κ
    htens he₁ hidem hK hinj s hs hcob a
  have hs' : ∀ a, e₁ • s a = s a := fun a => by
    obtain ⟨m, hm⟩ := hs a
    rw [← hm, DistribSMul.toLinearMap_apply, ← mul_smul, hidem]
  choose x hx using fun a => he₁ _ (hs' a)
  have h := hinj (fun a => ((ℓ : O) ^ e') • x a) (by
    convert hcob using 1
    funext g
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK a g g.2, map_smul, map_smul, LinearMap.smul_apply]) a
  rw [hx a, ← map_smul]
  exact h

end Formalism.RepresentationBoundsCohomology.BR
