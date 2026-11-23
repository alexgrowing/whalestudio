import Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheorem
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

set_option maxHeartbeats 4000000 in
theorem theorem_n_five_top_holds : WachTwistTheorem := by
  intro O _ _ _ X X' T T' Z p q b ha hb d _ _ R' _ hc Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' Kc k0 hEE hee hpts g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard hcard1
    sE tE δO ℓ cB what₂ qs deg s vhE H0 Sha hEsum hk0 NNc cols eO vδ N h0
    L _ _ _ tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _ cls pr Fs Im
    cT I γQ ζ ζO nQ u hE0 hδ0 hτ0 hne hIn0 hC hOne
  have hlen : ∀ c : Fin (t + 1), c ≠ 0 →
      (fun w => Module.length O (LinearMap.ker
        (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk c) (ζO w - 1)))) =
      fun w => IsDiscreteValuationRing.addVal O (ζO w - 1) := by
    intro c hc0
    funext w
    have h := KernelLengthBounds.length_ker_smul_pi (O := O) {a // bl a = c} (ζO w - 1)
    rw [hcard1 c hc0, Nat.cast_one, one_mul] at h
    exact h
  have h0b := bridgeRho O R' Tc G (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ δO ι colIdx D j e' Kc k0 ℓ what₂ s
    L tens v₁ κ (HcG 0) (Hc 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im hee hE0 hk0
    (fun m => by rw [algebraMap_smul]; exact hδ0 m) hIn0
  refine n5 O X X' T T' Z p q b ha hb d R' hc Tc G r χ E e₁ δ ι colIdx hinj D j e' Kc k0 hEE hee
    hpts g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard hcard1 sE tE δO ℓ cB what₂ qs
    (fun w => Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype)) deg
    (fun w => IsDiscreteValuationRing.addVal O (ζO w - 1)) s vhE H0 Sha hEsum hk0
    hE0 hδ0 hτ0 hne h0b.1 ?_ ?_ ?_
  · have h02 := h0b.2
    unfold OutRho at h02
    obtain ⟨F', Q', x1, x2, x3, x4⟩ := h02
    refine ⟨F', Q', ?_, ?_, ?_, ?_⟩
    · exact x1
    · exact x2
    · exact x3
    · exact x4
  · intro c hc2
    obtain ⟨a1, a2, a3, a4, a5, hIn⟩ := hC c hc2
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hc2
      simp at hc2
    have hout := bridgeChiC O R' Tc G (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ ι colIdx D j Kc k0 ℓ cB what₂ qs
      deg (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Vo VS Io IS I γQ ζ ζO nQ a1 a2 hk0 hIn
    rw [hlen c hc0] at hout
    unfold OutChi at hout
    exact ⟨a1, a2, a3, a4, a5, hout⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, hIn⟩ := hOne
    have hc0 : (⟨1, by omega⟩ : Fin (t + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hout := bridgeChiOne O R' Tc G (blockRestrictedRepresentationType bl ρk ⟨1, by omega⟩) r χ E e₁ δ δO ι colIdx D j e'
      Kc k0 ℓ cB what₂ qs deg (cT _) vhE (HcG _) (Hc _)
      (F _) Vo VS Io IS I γQ ζ ζO nQ u a1 a2 a3
      (fun m => by rw [algebraMap_smul]; exact a4 m) a5 a6 a7 a8 hIn
    rw [hlen _ hc0] at hout
    unfold OutChi at hout
    exact ⟨a1, a2, a3, a4, hout.1, hout.2⟩

end Formalism.RepresentationBoundsCohomology.BR
