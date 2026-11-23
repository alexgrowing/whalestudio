import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbsNormHalfDifferentDvdDiscr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem lowExponentBound_pos_below_last_index (D : D7) {j : ℕ} (CR : ℝ) {Tt cc : ℝ} (hj : j < D.R.m) (hT : 0 < Tt) (hc : 0 < cc) :
    0 < WeightFamilies.c1 D CR Tt cc j := by
  have hrho : 0 < WeightFamilies.rho D j := by
    unfold WeightFamilies.rho Ranks.sigW
    simp only
    omega
  have hf : 0 < D.R.f := by
    unfold Ranks.f Ranks.n
    positivity
  have hd : 0 < WeightFamilies.dP D j := by
    unfold WeightFamilies.dP
    positivity
  have hR : 0 < WeightFamilies.RRv D CR := by
    unfold WeightFamilies.RRv Formalism.BasicNotions.Host.rdE
    have h0 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    positivity
  unfold WeightFamilies.c1
  positivity

theorem sum_extendByZero_fin_eq_sum {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conjugateEmbedding_not_in_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA_eq {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA w) = ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i) := by
  classical
  simp only [GlobalTheory.ArcCM.absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum _ (by rw [← hD.2.1]; simp [Datum.mult, conjugateEmbedding_not_in_cmType _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) {j : ℕ} (hj : InR D j) (ka : WeightFamilies.Wt D j) :
    (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) + (fdeg D.host.E : ℝ) * ka.n ≤ ka.size := by
  obtain ⟨-, -, -, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hp
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (hJ j hj).2.1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg
    omega
  have ha := absA_wtA_eq T j (hp.2.2.2 j hj) hp.1 ka
  have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hm hr
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  rw [ha, hfd]
  unfold WeightFamilies.Wt.size
  push_cast at h3 ⊢
  nlinarith

theorem detectQ_of_known : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 < Tt → 0 < cc → DetectQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hjm hr hT hc F hF
  have hP : FactPrincipalDatum := Formalism.IndefR.Fin.factPrincipalDatum
  obtain ⟨hS, hM⟩ := GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hjm F
  rw [hM]
  intro k
  by_contra hk
  obtain ⟨Xx, hX, hg, hNA, hNC, hLa⟩ := exists_dataX_discr_absNorm hP D T h hG j hj T.σ₀ T.good_σ₀ k
  obtain ⟨hgood, hA, -, -, -, -, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr1, -⟩ := hJ j hj
  have hmod : ModelsAt (T.Q.Xo j) T.Q.c :=
    modelsAt_of_good_level hK _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (by omega) hgood
  have hFC : F.1 ∈ T.C j ka := F.2.1
  have hw := absA_add_le_size T h.pins hj ka
  obtain ⟨K₁, i1, i2, i3, d, hd, hne⟩ := GlobalTheory.T.exists_familyMember_functional_ne_zero hK D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) k Xx hX D.host.AA (wtA ka) ka.n (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)
    hmod (h.unf j hj T.σ₀ T.good_σ₀) hA hr (hG j hj T.σ₀ T.good_σ₀) (dom_wtA ka)
    (h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA ka)) (AA_ne_zero hP D) hLa hg (lowExponentBound_pos_below_last_index D CR hjm hT hc)
    (by linarith) F.1 (cusp_le_sec _ _ (T.U j) _ _ hFC) hS hk
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hq : (T.Q.Dw j).q = (D.R.sigW j).2 := (h.pins.2.2.2 j hj).2.1
  rw [hMg, hNA, hNC, hq] at hd
  exact hne (hF K₁ d hd)

end GlobalTheory.ArcCM
