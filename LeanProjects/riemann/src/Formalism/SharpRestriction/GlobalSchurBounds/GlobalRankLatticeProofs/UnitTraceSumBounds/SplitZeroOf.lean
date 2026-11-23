import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNorm
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhIsotropicOf

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSplit (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → SplitK D p →
    ∃ α ∈ OKp D lam, ∃ a b : ℤ_[p], α = (zc a, zc b) ∧ IsUnit (a - b)

def OkpNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 * α.2 = zc n

def OkpTwoUnits (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∀ α ∈ OKp D lam, ∃ β ∈ OKp D lam, ∃ γ ∈ OKp D lam, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ

theorem sDiff_of (H : SDiffOfGram) (D : D7) : GL3r7.StatementSymmetricDifference D := by
  intro hPG hbc p _ cc δ g hAt hp
  exact H p g (OKp D g.lam) hAt.2.2.2.2 (okp_zero D g.lam) (fun β hβ => okp_swap D g.lam β hβ)
    (fun β hβ γ hγ => okp_add D g.lam β γ hβ hγ) (fun β hβ γ hγ => okp_mul D g.lam β γ hβ hγ)
    (hPG p cc δ g hAt hp) (hbc p cc δ g hAt hp)

theorem splitZero_of (H : SplitZeroG) (D : D7) (hsp : OkpSplit D) (he : endInt D) (ha : addInt D) (hn : phNorm D)
    (hb : beConj D) (hB : beBiadd D) : splitZero D := by
  intro p _ cc δ g hAt hp hspl
  refine H p g (OKp D g.lam) hAt.2.2.2.2 hp (fun α hα => okpSwap_holds D p g.lam α hα)
    (fun α hα => he p cc δ g hAt α hα) (ha p cc δ g hAt).1 (fun α hα => hb p cc δ g hAt hp α hα)
    (hB p cc δ g hAt).1 ?_ (hsp p g.lam hp hspl)
  have h := hn p cc δ g hAt hp _ (okpNeg_holds D p g.lam)
  simpa using h

theorem beConj_of (H : BeConjOfNorm) (D : D7) (hN : OkpNorm D) (hU : OkpTwoUnits D) (he : endInt D) (ha : addInt D)
    (hn : phNorm D) (hB : beBiadd D) : beConj D := by
  intro p _ cc δ g hAt hp α hα
  have hadd : ∀ β ∈ OKp D g.lam, ∀ γ ∈ OKp D g.lam, β + γ ∈ OKp D g.lam :=
    fun β hβ γ hγ => okp_add D g.lam β γ hβ hγ
  exact H p g (OKp D g.lam) hAt.2.2.2.2 (fun β hβ => okpSwap_holds D p g.lam β hβ) hadd
    (fun β hβ => he p cc δ g hAt β hβ) (ha p cc δ g hAt).1 (fun β hβ => hN p g.lam β hβ)
    (fun β hβ => hU p g.lam hp β hβ) (fun β hβ => hn p cc δ g hAt hp β hβ) (hB p cc δ g hAt).1 α hα

end Formalism.MainNotions.Ext.CutA
