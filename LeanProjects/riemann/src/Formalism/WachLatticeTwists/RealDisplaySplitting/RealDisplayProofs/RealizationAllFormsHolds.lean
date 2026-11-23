import Formalism.WachLatticeTwists.RealDisplaySplitting.StatementA
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.TheoremNFiveAllForms

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll

set_option maxHeartbeats 4000000 in
theorem realization_all_forms_holds : AllSplitF := by
  intro ℓ _ O _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs deg s vhE H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam Cs _ _ cls pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HW HV₂ _ _ _ _ _ _ _ _ qW jT pairW HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4 hFix hBK hC hOne hrest
  obtain ⟨a1, a2, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, a7, a8, a9, a10, a11, a12, a13⟩ := hFix
  choose Kc hKc using fun l => compColK ℓ O R' Tc G Pe L r χ (D (colIdx l)) ince v₁ eve heve hse
    (Hfe₁ l) (Ff l) (e' (colIdx l)) (j (colIdx l)) (κ l) (κz l) (c8 l).1 (c8 l).2.2.1 (hLe l)
  choose k0 hk0 using fun l => compColk ℓ O R' Tc G PE (blockRestrictedRepresentationType bl ρk c1) r χ E δO (D (colIdx l)) incE
    evE hincE hact hevE hsE (HfE₁ l) (HfE₂ l) (e' (colIdx l)) (u l) (uz l) (huz l) (hu l) (hLE l)
  have hcont := hrest Kc k0 hKc hk0
  have hrat : ∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ)) := by
    intro x' hx'
    obtain ⟨δx, q1, q2, q3, q4, q5, q6⟩ := hrat0 x' hx'
    refine ⟨δx, q1, q2, q3, q4, q5, fun l => ?_⟩
    obtain ⟨Lx, w1, w2, w3, w4⟩ := q6 l
    obtain ⟨⟨Kz, hKz1, hKz2⟩, -⟩ := hKc l
    obtain ⟨⟨kz, hkz1, hkz2⟩, -, -⟩ := hk0 l
    exact ⟨Lx, w1, fun a s _ => colFun O R' Tc G Pe (EvalSp O d R' x') r χ (D (colIdx l)) ince (Hfe₁ l)
        (Lx : Set _) w2 (Kc l a) (Kz a) (hKz1 a) (hKz2 a) s,
      fun s _ => colFun O R' Tc G PE (EvalSp O d R' x') r χ (D (colIdx l)) incE (HfE₁ l)
        (Lx : Set _) w3 (k0 l) kz hkz1 hkz2 s, w4⟩
  have hRows : ∀ w ∈ what₂, InRowRho (blockRestrictedRepresentationType bl ρk 0) r χ E (D w) ε ρ₁ inc π γ (Hc 0 w) (F 0 w) (cls w)
      (pr w) (Fs w) (Im w) := by
    intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7⟩ := a12 w hw
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hBK w hw
    exact ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7,
      rowBK O _ (Hc 0 w) (HW w) (Cs w) (HV₂ w) (qW w) (jT w) (pr w) (pairW w) (HfW w)
        (Hf₂ w) (F 0 w) (Fs w) f2 f3 f4 f5 f6 f7⟩
  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg
        (fun w => cTB ℓ (sT w) (mT w) ((c : ℕ) - 1) (padicValNat ℓ (dT w)) (UT w))
        (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc2
    obtain ⟨g1, g2, g4, g5, g6, z1, z2, z3, z4, z5⟩ := hC c hc2
    exact ⟨rowsJ ℓ O R' Tc G (blockRestrictedRepresentationType bl ρk c) r χ E D what₂ deg (Hc c) (F c) t ((c : ℕ) - 1) uT wT sT
      mT dT UT (by have := c.2; omega) g6, z1, hcont c, z2, z3, z4, z5⟩
  obtain ⟨k1, k2, k3, k6, k7, k8, k9, z1, z2, z3, z4, z5⟩ := hOne
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ Fact.out hnu s₀ hs1 hs2 (ε gI) y u₁ hε t
  refine ⟨?_, ?_, ?_⟩
  · exact hF ι colIdx hinj D j e' Kc k0
      (fun x' hx' => by
        obtain ⟨δx, q1, q2, q3, q4, q5, q6⟩ := hrat x' hx'
        exact ⟨q5, q6⟩)
      ℓ cB what₂ qs deg s vhE H0 Sha (fun l g => (hk0 l).2.1 g) L tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂
      inc π γ lam Cs cls pr Fs Im
      (fun c w => cTB ℓ (sT w) (mT w) ((c : ℕ) - 1) (padicValNat ℓ (dT w)) (UT w))
      I γQ ζ ζO nQ u
      (inputs_from_selmer_inj O R' Tc G (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx D j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (Hc 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im
        ⟨a1, a2, fun l a g hg => (hKc l).2 a g hg, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, hcont 0, a7, a8,
          a9, a10, a11, hRows, a13⟩)
      (fun c hc2 => ⟨(hC c hc2).2.2.2.1, hC' c hc2⟩)
      ⟨fun l g hg m => (hk0 l).2.2 g hg m, k6, k7, k8,
        rowsJ ℓ O R' Tc G (blockRestrictedRepresentationType bl ρk _) r χ E D what₂ deg (Hc _) (F _) t 0 uT wT sT mT dT UT
          (by omega) k9, z1, hcont _, z2, z3, z4, z5⟩
  · show IsDiscreteValuationRing.addVal O δO = _
    rw [hδO]
    exact hv1
  · show IsDiscreteValuationRing.addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.RepresentationBoundsCohomology.SF
