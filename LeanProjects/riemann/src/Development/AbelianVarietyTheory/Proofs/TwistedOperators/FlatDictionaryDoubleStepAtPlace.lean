import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpandStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

theorem dblP_big : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hChr hArr hLoc hBes hJac
  intro t w hw p hp β r r₀ h hpts M hM φ v f hvf j hje hj
  have hstd : IsStdChar D ch.W.ψ (-1) := by rw [hch.weil.ψ]; exact s.std
  obtain ⟨hψ, hcond, -⟩ := hChr t w hw p hp
  have hm := D.R.m_even
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := hm; obtain ⟨b, hb⟩ := hje; omega
  have hj2 : j + 1 + 1 + 2 * ((D.R.m - 4 - j) / 2) + 2 = D.R.m := by omega
  have h0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
  have hL := hLoc t w hw p hp β r r₀ h hpts
  have t0 : topRank (locGrid ch.G t w) j + D.R.m = (locGrid ch.G t w).rank (D.R.m, j) + j + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have t1 : topRank (locGrid ch.G t w) (j + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1) + (j + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have t2 : topRank (locGrid ch.G t w) (j + 1 + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) + (j + 1 + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hc0 : topRank (locGrid ch.G t w) j + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by
    omega
  have hc1 : topRank (locGrid ch.G t w) (j + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1) := by
    omega
  have hc2 : topRank (locGrid ch.G t w) (j + 1 + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) := by
    omega
  have hodd : Odd (j + 1) := hje.add_one
  have hev2 : Even (j + 1 + 1) := hodd.add_one

  obtain ⟨T₁, hT₁, hO₁, Φ₁, hΦ₁, hTΦ₁⟩ := hArr t w hw p hp φ j (by omega) (v ⟨j, by omega⟩) (f ⟨j, by omega⟩)
    (hvf ⟨j, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h j * r₀ j) ((r₀ j)⁻¹ * r j) (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1))
    (hL j (by omega)).1 (hL (j + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1)) (frame hc0) (frame hc1)
  obtain ⟨T₂, hT₂, hO₂, Φ₂, hΦ₂, hTΦ₂⟩ := hArr t w hw p hp φ (j + 1) (by omega) (v ⟨j + 1, by omega⟩) (f ⟨j + 1, by omega⟩)
    (hvf ⟨j + 1, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1)) (h (j + 1 + 1) * r₀ (j + 1 + 1))
    ((r₀ (j + 1 + 1))⁻¹ * r (j + 1 + 1))
    (hL (j + 1) (by omega)).1 (hL (j + 1 + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1)) (frame hc1) (frame hc2)

  have hB0 := hBes t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h j * r₀ j) ((hL j (by omega)).2.1 hje) _ hc0
  have hJ1 := hJac t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1) * r₀ (j + 1)) (Or.inr ((hL (j + 1) (by omega)).2.2 hodd)) _ hc1
  have hB2 := hBes t w hw p hp M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1 + 1) * r₀ (j + 1 + 1)) ((hL (j + 1 + 1) (by omega)).2.1 hev2) _ hc2
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  have hxi := Witness.xi_ne p
  have es : (p.xi ^ ((D.R.m - 4 - j) / 2 + 1))⁻¹ * p.xi = (p.xi ^ ((D.R.m - 4 - j) / 2))⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hxi, mul_one]
  let Fd : GlobalTheory.LocMod.Dbl p (besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) (j + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (2 * ((D.R.m - 4 - j) / 2)) :=
    ⟨_, inv_ne_zero (pow_ne_zero _ hxi), _, _, _, _, _, _, hB0, hJ1, es ▸ hB2⟩

  obtain ⟨O₁, hOne₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
  obtain ⟨O₂, hOne₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
  have hv1 : ch.W.om (.mu t D.R.m j) ((h * r₀) j, (h * r₀) (j + 1)) (v ⟨j, by omega⟩) = T₁ O₁ := (hO₁ O₁ hOne₁).symm
  have hv2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r₀) (j + 1), (h * r₀) (j + 1 + 1)) (v ⟨j + 1, by omega⟩) = T₂ O₂ :=
    (hO₂ O₂ hOne₂).symm
  have hf1 : ch.W.om (.mu t D.R.m j) ((h * r) j, (h * r) (j + 1)) (f ⟨j, by omega⟩) = T₁ Φ₁ := by
    rw [hTΦ₁]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have hf2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r) (j + 1), (h * r) (j + 1 + 1)) (f ⟨j + 1, by omega⟩) = T₂ Φ₂ := by
    rw [hTΦ₂]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have E : ∀ (Φ : SchDown ch.G t) (g : Pts ch.G), conAt ch.W hM Φ g j =
      GlobalTheory.Unf.contr (linkAt hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (GlobalTheory.Unf.flatBF (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ hj')
            (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
          (ch.W.om (.mu t D.R.m j) (g j, g (j + 1)) (Φ ⟨j, by omega⟩)))
        (GlobalTheory.Unf.flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
            (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
          (ch.W.om (.mu t D.R.m (j + 1)) (g (j + 1), g (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩))) := by
    intro Φ g
    unfold conAt
    rw [dif_neg h0]
    exact dif_pos hj'
  rw [E v (h * r₀), E f (h * r)]
  rw [hv1, hv2, hf1, hf2]
  have hz : ∀ (S' : Finset I), (∀ q₁ q₂, ∑ i ∈ S', x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∀ q,
      GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w) (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1)
        (0 : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
          (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1)) (Kw w))).1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S', x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
    intro S' hS' q
    rw [hS' q.1 q.2]
    simp [GlobalTheory.LocFlat.contr, GlobalTheory.LocFlat.flCol, GlobalTheory.RootEx.opE, GlobalTheory.StepData.hat]
  refine ⟨fun hvan => ?_, fun hq => ?_⟩
  · refine Eq.trans (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond
      ((D.R.m - 4 - j) / 2) _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc (hz S hvan)).symm ?_
    exact (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I ∅ x Ξ₁ Ξ₂ c₁ c₂ (by simp)
      (hz ∅ fun _ _ => Finset.sum_empty)).trans Finset.sum_empty
  · have hloc : ∀ q, GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w)
        (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1) Φ₁.1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
      intro q
      rw [← hq q, show Φ₁.1 = _ from funext hΦ₁, show Φ₂.1 = _ from funext hΦ₂]
      unfold facAt locA
      rw [dif_neg (show ¬ j + 2 * 0 + 2 = (locGrid ch.G t w).m from h0),
        dif_pos (show j + 2 * (((locGrid ch.G t w).m - 4 - j) / 2 + 1) + 2 = (locGrid ch.G t w).m from hj')]
      rfl
    exact GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hloc

end GlobalTheory.FlatPlace
