import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum.BasePair

variable {D : D7}

theorem placeIdem_mul_eq_zero {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hne : v' ≠ v) : ε' * ε = 0 := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  have e : α' * α = 0 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw; rw [h2' w hne.symm, zero_mul]
    · rw [h2 w hw, mul_zero]
  show pairA D.host.F 0 α' * pairA D.host.F 0 α = 0
  have e2 : pairA D.host.F 0 α' * pairA D.host.F 0 α = pairA D.host.F 0 (α' * α) := Prod.ext (mul_zero _) rfl
  rw [e2, e]
  rfl

theorem split_mul_nonSplit {e : AE D} (he : IsSplitIdem D e) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : (e + cA D e) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
  obtain ⟨-, -, v', ε', h', he'⟩ := id he
  by_cases hvv : v' = v
  · subst hvv
    have : ε' = ε := by
      obtain ⟨α, rfl, h1, h2⟩ := hv.1
      obtain ⟨α', rfl, h1', h2'⟩ := h'
      have : α' = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
        by_cases hw : w = v'
        · subst hw; rw [h1, h1']
        · rw [h2 w hw, h2' w hw]
      rw [this]
    subst this
    exact absurd ⟨e, he, he'⟩ hv.2
  · rw [he', ← map_mul, placeIdem_mul_eq_zero hv.1 h' hvv, map_zero]

theorem unramAt_of_unramOutside {χ : (AE D)ˣ →* Circle} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hs : GlobalTheory.ExportSeries.SplitSet Q)
    (hu : GlobalTheory.ExportSeries.UnramOutside χ Q) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε χ := by
  intro x hx i1 i2
  have hinf : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -⟩ := hv.1
    exact TensorProduct.zero_tmul _ _
  have hx1 : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, hinf, zero_mul, map_sub, map_one] at this
    exact sub_eq_zero.1 this.symm
  refine hu x hx1 i1 i2 ?_
  have h0 : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_eq_zero fun PP hPP => split_mul_nonSplit (hs.isIdemAt hPP).1 hv
  calc (idem Q + cA D (idem Q)) * (x : AE D)
      = (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) + (idem Q + cA D (idem Q)) := by
        rw [mul_assoc, hx]; ring
    _ = idem Q + cA D (idem Q) := by rw [h0, zero_mul, zero_add]

theorem unramAt_mul {ε : AF D.host.F} {χ χ' : (AE D)ˣ →* Circle} (h : GlobalTheory.WeilParts.UnramAt ε χ)
    (h' : GlobalTheory.WeilParts.UnramAt ε χ') : GlobalTheory.WeilParts.UnramAt ε (χ * χ') := fun x a b c => by
  rw [MonoidHom.mul_apply, h x a b c, h' x a b c, one_mul]

theorem unramAt_inv {ε : AF D.host.F} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.WeilParts.UnramAt ε χ) :
    GlobalTheory.WeilParts.UnramAt ε χ⁻¹ := fun x a b c => by
  rw [MonoidHom.inv_apply, h x a b c, inv_one]

end GlobalTheory.SingleDatum.BasePair

open GlobalTheory.SingleDatum.BasePair in

theorem GlobalTheory.SingleDatum.vacPair_of_good : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ ω : PairRep V W, B.IsWeil 1 ω → VacPair B.F.ψ B.F.θ V W (B.mu * 1) (B.mu * 1 * B.eta⁻¹) ω B.F.ΛS B.F.ΛT B.F.sT B.F.f₀ := by
  intro D V W B hB hS ω hω
  obtain ⟨hg, hsig, hV, hW, hstd⟩ := hS
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = W.rank := fun τ => by
    have := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hB.sigOK (tauE D τ))).1
    rw [← hB.sig τ] at this
    exact this
  obtain ⟨s, hs⟩ := hB.odd
  have expMu : ∀ τ, ∃ a : ℤ, HasInfExp D (B.mu * 1) τ a := fun τ => by
    refine ⟨B.w.c τ - s + B.w.q τ, ?_⟩
    have e : (((B.w.c τ - s + B.w.q τ : ℤ)) : ℚ) = (B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2 := by
      have h1 : (B.w.p τ : ℚ) + B.w.q τ = 2 * s + 1 := by exact_mod_cast (hpq τ).trans hs
      push_cast
      linear_combination (1 / 2 : ℚ) * h1
    rw [mul_one, e]
    exact GlobalTheory.RealFockAction.hasInfExp_mul_of_isOpen_ker (hB.inf τ) hB.de.isOpen
  have hPg : GlobalTheory.ExportSeries.SplitSet B.G.Pg := by
    obtain ⟨P, h1, -, h3⟩ := hB.places.split
    exact h3.mono h1
  refine ⟨⟨hω, hB.frame.vac.2.inf, hg, hB.even, hsig, hB.sigOK, expMu, fun τ => ?_, fun v ε hv => ?_, ⟨_, hB.eta⟩⟩,
    ?_, hV, hW, hB.frame.sdS, hB.frame.sdT, hstd, hB.frame.cartT, hB.frame.vac⟩
  · obtain ⟨a, ha⟩ := expMu τ
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hB.eta.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + (W.rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [hs]; push_cast; ring
    rw [e]
    exact h3
  · have u1 : GlobalTheory.WeilParts.UnramAt ε (B.mu * 1) := by
      rw [mul_one]
      exact unramAt_mul (unramAt_of_unramOutside hPg hB.unram hv) (unramAt_of_unramOutside hB.de.split hB.de.unram hv)
    exact ⟨u1, unramAt_mul u1 (unramAt_inv (GlobalTheory.AdTh.PairModel.unramAt_of_everywhere hB.eta.2.1 hv.1))⟩
  · have h1 : 0 < W.rank := by rw [hs]; omega
    exact (lt_of_lt_of_le h1 B.hr).ne'
