import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfPhAt
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

section

variable {p : ℕ} [Fact p.Prime]

theorem coefWf_zero {σ : Type} : CoefWf (0 : MvPowerSeries σ ℂ_[p]) := fun n => ⟨0, by
  rw [map_zero, mul_zero]; exact (Wp p).zero_mem⟩

theorem coefWf_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p]) (h : ∀ i ∈ s, CoefWf (f i)) :
    CoefWf (∑ i ∈ s, f i) :=
  Finset.sum_induction f CoefWf (fun _ _ => coefWf_add) coefWf_zero h

end

theorem phDualW_of (HA : AddPtW) (HL : LinPtW) (D : D7) : StatementPhaseDualWitt D := by
  intro hph _ ha he hd p _ cc δ g hA h5 hI hW κ ι _ _ b b' hb hb' hdu
  have hOk := hA.2.2.2.2
  have hP : CoefWf g.ph := hph p cc δ g hA h5 hI hW
  have hF := (ha p cc δ g hA).2 hW
  have hmem : ∀ (e : ι ⊕ ι) (k : κ), Sum.elim b b' e k ∈ OKp D g.lam := by
    rintro (e | e) k
    · exact hb e k
    · exact hb' e k
  have h1 : CoefWf (g.PhOn (Sum.elim b b')) :=
    coefWf_sum _ _ fun k _ => coefWf_phAt g hP
      (HL p g hOk hF _ _ (fun e => he p cc δ g hA h5 hI hW _ (hmem e k)) _ _ fun e => ptW_X e)
  have h2 : CoefWf (g.beSum ι) :=
    coefWf_sum _ _ fun e _ => coefWf_be HA g hOk hF hP (ptW_X _) (ptW_X _)
  exact ⟨h1, simeqW_of h1 h2 (hd p cc δ g hA (by omega) κ ι b b' hb hb' hdu)⟩

theorem sDiffW_of (HA : AddPtW) (HM : MulPtW) (HL : LinPtW) (D : D7) : StatementSymmetricDifferenceWitt D := by
  intro hph _ hadd he hd p _ cc δ g hA h5 hI hW κ ι ι' _ _ _ a a' ha hb
  have hOk := hA.2.2.2.2
  have hP : CoefWf g.ph := hph p cc δ g hA h5 hI hW
  have hF := (hadd p cc δ g hA).2 hW
  have hE := he p cc δ g hA h5 hI hW
  have hmem : ∀ (e : ι ⊕ ι') (k : κ), Sum.elim a a' e k ∈ OKp D g.lam := by
    rintro (e | e) k
    · exact hb' a ha e k
    · exact hb' a' hb e k
  have hV : ∀ {ι₀ : Type} [Fintype ι₀] (c : ι₀ → κ → ℂ_[p] × ℂ_[p]), (∀ e k, c e k ∈ OKp D g.lam) →
      ∀ w : ι₀ → MvPowerSeries (ι ⊕ ι') ℂ_[p], (∀ e, PtW (w e)) → CoefWf (PhV g c w) := fun c hc w hw =>
    coefWf_sum _ _ fun k _ => coefWf_phAt g hP (HL p g hOk hF _ _ (fun e => hE _ (hc e k)) _ _ hw)
  have h1 : CoefWf (sdL g a a') :=
    coefWf_sub (coefWf_sub (hV _ hmem _ fun e => ptW_X e) (hV a ha _ fun e => ptW_X _)) (hV a' hb _ fun e => ptW_X _)
  have h2 : CoefWf (sdR g a a') :=
    coefWf_sum _ _ fun f _ => coefWf_sum _ _ fun f' _ =>
      coefWf_be HA g hOk hF hP (HM p g hOk _ (hE _ (okp_hP D g.lam _ _ (ha f) (hb f'))) _ _ (ptW_X _)) (ptW_X _)
  have h3 : CoefWf (sdR' g a a') :=
    coefWf_sum _ _ fun f _ => coefWf_sum _ _ fun f' _ =>
      coefWf_be HA g hOk hF hP (ptW_X _)
        (HM p g hOk _ (hE _ (okp_swap D g.lam _ (okp_hP D g.lam _ _ (ha f) (hb f')))) _ _ (ptW_X _))
  obtain ⟨d1, d2⟩ := hd p cc δ g hA (by omega) κ ι ι' a a' ha hb
  exact ⟨h1, simeqW_of h1 h2 d1, simeqW_of h1 h3 d2⟩
where
  hb' {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {ι₀ κ : Type} (c : ι₀ → κ → ℂ_[p] × ℂ_[p])
      (h : ∀ e, InOKp D lam (c e)) (e : ι₀) (k : κ) : c e k ∈ OKp D lam := h e k

end Formalism.MainNotions.Ext
