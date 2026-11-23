import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTSupConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple

noncomputable section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

variable {D : D7}

def GoodMod (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) : Prop :=
  𝔪 ≠ ⊥ ∧ 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ ∧ IsCoprime 𝔪 (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) ∧
    ∀ v, v ∈ Sf ↔ ∃ w : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ w.asIdeal ∧ w.under (𝓞 D.host.F) = v

abbrev stdLat (V : HSp D) : Lat V := Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank

def locNorm (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset,
    (((Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * a * a'))⁻¹ * glVol (Ideal.absNorm w : ℝ) a)

def locIdx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset, blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a a'

def vacNorm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (a d : ℕ) : ℝ :=
  Formalism.MainNotions.StandardLatticesGL3.nrm1Sq (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) (Formalism.MainNotions.GL3Theta.th0 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0) ^ (Formalism.MainNotions.TaylorLogMetric.fF D * a * d)

def mass (D : D7) (N : ℕ) : ℂ := ∑ᶠ x : Cls D N (intG D N), ((gam D (intG D N) x.out : ℂ))⁻¹

def fockSum (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  ∑ T : Tup D a d n, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T)

theorem goodMod_top (D : D7) : GoodMod D ⊤ ∅ := by
  refine ⟨top_ne_bot, top_sup_eq _, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left, fun v => ?_⟩
  simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
  exact fun w h => absurd (top_le_iff.1 h) w.isPrime.ne_top

theorem goodMod_modT {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (G : GridData L sc) (t : T) : GoodMod D (modT G t) (sfB G t) := by
  refine ⟨GlobalTheory.FunObj.StdDatum.TwBig.modT_ne_bot G t, GlobalTheory.SqTop.modT_sup_conj hL G t,
    GlobalTheory.BotPairSmallTw.modT_isCoprime_two_q hL hpq hpq' G t, fun v => ?_⟩
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), modT G t ≤ w.asIdeal ↔ w ∈ locPl G t := by
    intro w
    have hp := w.isPrime
    have hc : ∀ v, SqNum.condExp G.pl v ≠ 0 := fun v => by unfold SqNum.condExp; split_ifs <;> omega
    unfold modT condE
    rw [hp.mul_le, hp.prod_le, hp.prod_le]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨w', hw', h⟩)
      · have h1 : (G.pl.w v).asIdeal ≤ w.asIdeal := (Ideal.IsPrime.pow_le_iff (hc v)).1 h
        have h2 : G.pl.w v = w := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hp.ne_top h1)
        unfold locPl Places.W0
        exact Finset.mem_union_left _ (h2 ▸ Finset.mem_image_of_mem _ hv)
      · have h2 : w' = w := HeightOneSpectrum.ext (w'.isMaximal.eq_of_le hp.ne_top h)
        subst h2
        exact (Finset.mem_filter.1 hw').1
    · intro hw
      by_cases h0 : w ∈ G.pl.W0
      · unfold Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        exact Or.inl ⟨v, hv, Ideal.pow_le_self (hc v)⟩
      · exact Or.inr ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, le_rfl⟩
  unfold sfB
  simp only [Finset.mem_image, key]

end GlobalTheory.NormRatio
