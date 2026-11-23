import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem eq_under {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hv : SplitAt D v e) : v = P.under (𝓞 D.host.F) := by
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e hv
  have hPQ : Q = P := GlobalTheory.PlaceVec.isIdemAt_inj hQ hP
  subst hPQ
  exact HeightOneSpectrum.ext hQv.symm

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

theorem places : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D), c.Is → ∀ (f : c.Pg → GlobalTheory.FinPl.Pl D) (e : c.Pg → AE D),
    (∀ PP, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) →
    (∀ PP, ∃ ε, IsPlaceIdem D (f PP) ε ∧ e PP + cA D (e PP) = algebraMap (AF D.host.F) (AE D) ε) →
    Function.Injective f ∧ ∀ v, v ∈ c.S ↔ v ∈ Set.range f := by
  intro D c hc f e he hf
  have key : ∀ PP, f PP = PP.1.under (𝓞 D.host.F) := by
    intro PP
    obtain ⟨ε, hε, hsum⟩ := hf PP
    exact eq_under (he PP) (splitAt_of (he PP).1 hε hsum)
  refine ⟨fun PP PP' hPP => ?_, fun v => ?_⟩
  · rw [key, key] at hPP
    obtain ⟨E', ⟨es, hes, hsum⟩, h0⟩ := hc.split
    have h0' := h0
    rw [hsum, map_sum, Finset.sum_mul_sum, ← Finset.sum_product'] at h0'
    have hz : ∀ x ∈ c.Pg ×ˢ c.Pg, es x.1 * cA D (es x.2) = 0 :=
      GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) GlobalTheory.PlaceVec.natCast_mul_eq_zero
      (fun x : Formalism.L2.DIV.Pl D.host.E × Formalism.L2.DIV.Pl D.host.E => es x.1 * cA D (es x.2)) (c.Pg ×ˢ c.Pg) (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hi
        rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]) h0'
    have ha := hes PP.1 PP.2
    have hb := hes PP'.1 PP'.2
    have hab : es PP.1 * cA D (es PP'.1) = 0 := hz (PP.1, PP'.1) (Finset.mem_product.2 ⟨PP.2, PP'.2⟩)
    obtain ⟨va, hva⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff _).1 ha.1
    obtain ⟨vb, hvb⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff _).1 hb.1
    have e1 := eq_under ha hva
    have e2 := eq_under hb hvb
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero ha.1 hb.1 with h | h
    · exact Subtype.ext (GlobalTheory.PlaceVec.isIdemAt_inj ha (h ▸ hb))
    · exfalso
      refine ne_zero_of_isIdemAt ha ?_
      have hv : va = vb := by rw [e1, e2, hPP]
      subst hv
      have q1 : es PP.1 * (es PP.1 + cA D (es PP.1)) = es PP.1 := by rw [mul_add, hva.1, hva.2.1, add_zero]
      rw [hva.2.2, ← hvb.2.2, mul_add, h, hab, add_zero] at q1
      exact q1.symm
  · classical
    simp only [GlobalTheory.ChainOnto.Com.S, Finset.mem_image, Set.mem_range]
    constructor
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨⟨PP, hPP⟩, key _⟩
    · rintro ⟨PP, rfl⟩
      exact ⟨PP.1, PP.2, (key PP).symm⟩

end GlobalTheory.LevelPlaces
