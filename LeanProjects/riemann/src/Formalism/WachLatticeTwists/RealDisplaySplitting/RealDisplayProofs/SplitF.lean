import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.RealizationAllFormsHolds
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.TheoremNFiveSplitRankForm

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll

set_option maxHeartbeats 4000000 in
theorem split_all_second_form : SplitAllF := by
  intro ℓ _ O _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs deg s vhE H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam Cs _ _ _ _ cls pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HW HV₂ _ _ _ _ _ _ _ _ qW jT pairW HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4 hFix hBK hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA Zc clsV H₁ _ _ _ _ Hf₁ gR
    τH DatH bH wH mH hrows hseq hcls hclsV hliftR hH0 hJC hJR
  obtain ⟨key, kδ1, kδ2⟩ := realization_all_forms_holds ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc G r χ E e₁ δ ι colIdx hinj
    D j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs deg s vhE H0
    Sha uT wT sT mT dT UT hEsum hF L tens v₁ κ V iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam Cs cls pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HW HV₂ qW jT pairW HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4 hFix hBK hC hOne hrest
  have hrow : ∀ w ∈ cols, conj w ∈ what₂ := fun w hw => hrows ▸ Finset.mem_image_of_mem conj hw
  have hj : ∀ w ∈ cols, j w ≤ nlam w * m := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hJC w hw
    have := Formalism.RepresentationBoundsCohomology.jumpsColumn (Fin (nlam w)) (cloudC w) (lowsC w) m (j w) (h0C w) h1 h2 h3 h4
    simpa [Fintype.card_fin] using this
  have hdim : ∀ w ∈ cols, Module.finrank (FractionRing O) (Hf₂ (conj w)) ≤ nlam w * m := by
    intro w hw
    obtain ⟨h1, h2, hfd, h3, h4⟩ := hJR w hw
    have := Formalism.RepresentationBoundsCohomology.jumpsRow (Fin (nlam w)) (cloudR w) (lowsR w) m
      (Module.finrank (FractionRing O) (Hf₂ (conj w))) (h0R w) h1 h2 h3 h4
    simpa [Fintype.card_fin] using this
  have heq : ∀ w ∈ cols,
      (∑ τ, Formalism.RepresentationBoundsCohomology.negCount ((cloudR w τ + lowsR w τ).map (fun u => -u - 1))) =
        (∑ τ, Formalism.RepresentationBoundsCohomology.negCount (cloudC w τ + lowsC w τ)) →
      Module.finrank (FractionRing O) (Hf₂ (conj w)) = j w := by
    intro w hw hc
    obtain ⟨-, -, h3, h4⟩ := hJC w hw
    obtain ⟨-, -, -, k3, k4⟩ := hJR w hw
    rw [h3, k3, h4, k4, hc]
  have hL0 : ∀ w ∈ cols,
      Module.length O (Fs (conj w) ⧸ (Im (conj w)).comap (Fs (conj w)).subtype) ≤
      ((Module.finrank (FractionRing O) (Hf₂ (conj w)) : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
        N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO) := by
    intro w hw
    obtain ⟨-, -, hfd, -, -⟩ := hJR w hw
    obtain ⟨hfin, -, -, -, -, -, hFs⟩ := hBK (conj w) (hrow w hw)
    have hpre : ∀ x ∈ Fs (conj w), jT (conj w) x ∈ Hf₂ (conj w) := by
      intro x hx
      rw [hFs] at hx
      exact hx
    have hlift : ∀ x ∈ Fs (conj w), ((ℓ : O) ^ e' w) • x ∈ Im (conj w) := by
      intro x hx
      rw [(hliftR w hw).1]
      exact srcO ℓ O _ _ (Hf₁ (conj w)) (Fs (conj w)) (gR (conj w)) (e' w) (hliftR w hw).2 x hx
    have hkt := kerTors O (D (conj w)) T₂ V₂ ({a // bl a = 0} → KO O) (Cs (conj w)) (HV₂ (conj w))
      (resRep ρ₂ (D (conj w))) (resRep ρV (D (conj w))) (resRep ρA (D (conj w))) iV qA
      (Zc (conj w)) (cls (conj w)) (Fs (conj w)) (clsV (conj w)) (jT (conj w)) (hseq.res _)
      (hcls w hw) (ko_pi_torsion O _) (fun a ha => (hclsV w hw a ha).1)
      (fun a ha => (hclsV w hw a ha).2)
    have hrk : Module.finrank O (Fs (conj w)) ≤ Module.finrank (FractionRing O) (Hf₂ (conj w)) :=
      rankLe O (Cs (conj w)) (HV₂ (conj w)) (jT (conj w)) (Fs (conj w)) (Hf₂ (conj w)) hfd
        hpre hkt
    refine rowCost O (Cs (conj w)) (Fs (conj w)) (Im (conj w)) {a // bl a = 0} ℓ (e' w)
      (c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))))
      (Module.finrank (FractionRing O) (Hf₂ (conj w))) (finSub O (Cs (conj w)) (Fs (conj w)) hfin) hlift ?_ hrk
    refine ⟨LinearMap.ker (coD0 (resRep ρA (D (conj w)))), ?_, ?_⟩
    · intro x hx
      refine h_zero_invariants_killed ℓ O G _ ρA (D (conj w)) (DatH w) (bH w) (wH w) (mH w) _ (hH0 w hw).1
        (hH0 w hw).2.toIn x fun g hg => ?_
      have h1 := congrFun (LinearMap.mem_ker.1 hx) (⟨g, hg⟩ : D (conj w))
      exact sub_eq_zero.1 h1
    · exact torsion_le_h_zero O (D (conj w)) T₂ V₂ ({a // bl a = 0} → KO O) (Cs (conj w))
        (resRep ρ₂ (D (conj w))) (resRep ρV (D (conj w))) (resRep ρA (D (conj w))) iV qA
        (Zc (conj w)) (cls (conj w)) (Fs (conj w)) (hseq.res _) (hcls w hw)
  have hL : ∀ w ∈ cols,
      Module.length O (Fs (conj w) ⧸ (Im (conj w)).comap (Fs (conj w)).subtype) ≤
      ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
        N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO) := by
    intro w hw
    refine (hL0 w hw).trans (add_le_add (mul_le_mul' ?_ le_rfl) le_rfl)
    exact_mod_cast hdim w hw
  refine ⟨hj, hdim, heq, hL0, hL, ?_, ?_, kδ1, kδ2⟩
  · have hfold := splitFold (vcc T Z (p π')) what₂ cols conj
      (fun w => Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype))
      (fun w => eO * (e' w : ℕ∞)) (fun w => eO * (e' w : ℕ∞) + vδ) (fun _ => 2 * vδ) h0
      (fun w => ((Module.finrank (FractionRing O) (Hf₂ (conj w)) : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO))
      (fun w => N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO))
      j j
      (s + ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 +
        (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1))
      (by simpa only [add_assoc] using key) hrows (fun _ _ => le_rfl) hL0
    simpa only [add_assoc] using hfold
  · have hfold := splitFold (vcc T Z (p π')) what₂ cols conj
      (fun w => Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype))
      (fun w => eO * (e' w : ℕ∞)) (fun w => eO * (e' w : ℕ∞) + vδ) (fun _ => 2 * vδ) h0
      (fun w => ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO))
      (fun w => N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO))
      j (fun w => nlam w * m)
      (s + ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 +
        (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1))
      (by simpa only [add_assoc] using key) hrows hj hL
    simpa only [add_assoc] using hfold

end Formalism.RepresentationBoundsCohomology.SF
