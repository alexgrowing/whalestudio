import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.KeyMul
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LiftBound
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.YGenCongr

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem bridgeRho : StatBridgeRho := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ δO ι _ _ colIdx D j e' Kc k0 ℓ what₂ s
    L _ _ _ tens v₁ κ HcG Hc F Vo Io ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _ cls pr Fs Im
    hidem hE hk0 hδ hIn
  obtain ⟨htens, he₁, hK, hBK, hC3, hcont, hres, hG4, hinc, hπ, hγ, hrow, hsel⟩ := hIn
  refine ⟨fun l => liftBound O A T' G M L r χ e₁ (D (colIdx l)) (j (colIdx l)) (Kc l) ℓ
    (e' (colIdx l)) tens v₁ (κ l) htens he₁ hidem (hK l)
    (fun x hx a => by rw [hC3 l x hx a, map_zero]), ?_⟩
  refine ⟨F, HcG ⊓ ⨅ v, unrH1 _ (Io v), ?_, ?_, ?_, hsel⟩
  · intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, c1, c2, c3, hH2, hTate, hImf, hle, hF⟩ := hrow w hw
    have hcup := rowCup O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (ε.comp (D w).subtype) T₁ T₂
      (resRep ρ₁ (D w)) (resRep ρ₂ (D w)) inc π γ lam C₁ CN2 CN CA CP (fun g b => hinc g b)
      (fun g m => hπ g m) hγ c1 c2 c3 hH2
    obtain ⟨B, hB1, hB2, hB3⟩ := rowRho O (D w) M (resRep (uRep O (M := M) r χ) (D w))
      (ε.comp (D w).subtype) T₁ T₂ (resRep ρ₁ (D w)) π γ C₁ CP (Hc w) (Cs w) (cls w) (pr w)
      (Fs w) (Im w)
      (Set.range (fun φ => restrictCocycles1 (uRep O (M := M) r χ) (D w)
        (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l))
          Kc k0 φ)))
      hTate hImf hle (by rintro _ ⟨φ, rfl⟩; exact hres w hw (hcont φ))
      (by rintro _ ⟨φ, rfl⟩ a ha hC; exact hcup φ a ha hC)
    exact ⟨B, hF ▸ hB1, by rw [hF]; exact hB2, fun h => hB3 _ ⟨h, rfl⟩⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    exact (colRho O A T' G M L r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 ℓ (fun l => e' (colIdx l)) tens v₁ κ
      htens he₁ hK hE hk0 hδ h l).2 (F (colIdx l)) (hBK l)
  · intro h
    exact ⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩

theorem bridgeChiC : StatBridgeChiC := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ _ colIdx D j Kc k0 ℓ cB what₂ qs
    deg cT s HcG Hc F Vo VS Io IS I γ ζ ζO n he₁ hE hk0 hIn
  obtain ⟨hrow, hq, hcont, hres, hG4, hG5, hsel⟩ := hIn
  refine ⟨F, (HcG ⊓ (⨅ v, unrH1 _ (Io v)) ⊓ ⨅ v, unrH1 _ (IS v)), ?_, ?_, ?_, ?_, hsel⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hrow w hw
    exact rowTB O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) ℓ (cT w) cB (deg w) (Hc w) (F w) h1 h2
      (fun φ => hres w hw (hcont φ)) h3 h4
  · intro w hw
    obtain ⟨hF, a1, a2, a3, a4, a5, a6⟩ := hq w hw
    obtain ⟨-, B, b1, b2, b3⟩ := qPlace O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (I w) (γ w) (ζ w)
      (ζO w) (n w) a1 a2 a3 a4 a5 a6
    exact ⟨B, hF ▸ b1, by rw [hF]; exact b2, b3⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    rw [colChiC O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 he₁ hE hk0 h l]
    exact (F (colIdx l)).zero_mem
  · intro h
    exact ⟨⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩,
      (Submodule.mem_iInf _).2 fun v =>
      (unrS O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (IS v) (hG5 v) h).2⟩

theorem bridgeChiOne : StatBridgeChiOne := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ δO ι _ _ colIdx D j e' Kc k0 ℓ cB what₂ qs
    deg cT s HcG Hc F Vo VS Io IS I γ ζ ζO n u hu he₁ hE hδ hk huI huF hFc hIn
  obtain ⟨hrow, hq, hcont, hres, hG4, hG5, hsel⟩ := hIn
  refine ⟨fun l => ?_, F, (HcG ⊓ (⨅ v, unrH1 _ (Io v)) ⊓ ⨅ v, unrH1 _ (IS v)),
    ?_, ?_, ?_, ?_, hsel⟩
  · obtain ⟨g, hg, hg1⟩ := huF l
    exact ⟨g, hg, 1, isUnit_one, fun m => by rw [hk l g hg m, hg1]⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hrow w hw
    exact rowTB O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) ℓ (cT w) cB (deg w) (Hc w) (F w) h1 h2
      (fun φ => hres w hw (hcont φ)) h3 h4
  · intro w hw
    obtain ⟨hF, a1, a2, a3, a4, a5, a6⟩ := hq w hw
    obtain ⟨-, B, b1, b2, b3⟩ := qPlace O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (I w) (γ w) (ζ w)
      (ζO w) (n w) a1 a2 a3 a4 a5 a6
    exact ⟨B, hF ▸ b1, by rw [hF]; exact b2, b3⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    exact hFc l ((colChiOne O A T' G M r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 ℓ (fun l => e' (colIdx l)) u
      hu he₁ hE hδ hk h l).2.2 (I (colIdx l)) (huI l))
  · intro h
    exact ⟨⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩,
      (Submodule.mem_iInf _).2 fun v =>
      (unrS O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (IS v) (hG5 v) h).2⟩

end Formalism.RepresentationBoundsCohomology.BR
