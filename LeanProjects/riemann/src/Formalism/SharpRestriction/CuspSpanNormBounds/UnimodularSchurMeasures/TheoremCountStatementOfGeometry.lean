import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnTwoPowMul
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.DedekindResidueLeOfAdmitted
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDAll
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.NearCountOfLayers

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_eps (X : CData) (cε : ℝ) : ℝ := Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f

def GeoS (X : CData) (cε Cv Cd Cq : ℝ) : Prop :=
  ∃ (S : CSize X) (volK : ℝ), S.Strata ∧ S.Density ∧ S.KappaVol Cv ∧
    S.NearLayers (cn_eps X cε) (3 * Real.sqrt ((X.I.n : ℝ) * cn_eps X cε)) ∧ S.SepStep ∧
    (1 ≤ X.qq → S.DeepStepsQ volK Cd Cq)

def GeoC (X : CData) (Cres cε Cv Cd Cq : ℝ) : Prop := cn_ResBound X Cres ∧ GeoS X cε Cv Cd Cq

theorem residue_bound_of_admitted (D : Formalism.BasicNotions.D7) (Cres : ℝ) (h : adm7 D Cres) (X : CData) : cn_ResBound X Cres := by
  have h1 := dedekind_residue_le_of_admitted D Cres h X.I.E X.I.cm.cmUnram
  have h2 := qt_finrank X.I.E X.I.cm.cmUnram
  have h3 : Module.finrank ℚ X.I.F * Module.finrank X.I.F X.I.E = Module.finrank ℚ X.I.E :=
    Module.finrank_mul_finrank ℚ X.I.F X.I.E
  rw [X.I.cm.deg2] at h3
  have h4 : Formalism.HermitianLatticesTheory.fDeg X.I.E = X.I.f := by
    unfold AutInst.f
    omega
  rw [h4] at h1
  exact h1

theorem cn_x_nonneg (X : CData) : 0 ≤ (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ) :=
  mul_nonneg (by positivity) (Real.log_natCast_nonneg _)

theorem cn_exp_mono (X : CData) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    Real.exp (-(c₂ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) ≤
      Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := by
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right h (cn_x_nonneg X)
  nlinarith

theorem cn_probMod_mono (X : CData) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) {Mod : Set X.I.GA} (hP : X.ProbMod c₂ Mod) : X.ProbMod c₁ Mod := by
  unfold CData.ProbMod at *
  refine le_trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg) hP
  have := cn_exp_mono X h
  linarith

theorem cn_nearStep_mono (X : CData) (hDs : 0 ≤ X.Ds) {c₁ c₂ εN : ℝ} (h : c₁ ≤ c₂) {Mod : Set X.I.GA}
    (hP : X.NearStep εN c₂ 1 Mod) : X.NearStep εN c₁ 1 Mod := by
  unfold CData.NearStep at *
  refine le_trans hP (ENNReal.ofReal_le_ofReal ?_)
  have := cn_exp_mono X h
  gcongr

theorem cn_mod : ∃ c₁ cb : ℝ, 0 < c₁ ∧ 0 < cb ∧ ∀ Cd Cq : ℝ, 1 ≤ Cd → 0 ≤ Cq → 16 * Cq ≤ Cd → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ Cv Cres A : ℝ, 1 ≤ Cv → 1 ≤ A →
    ∃ n₁ : ℕ, ∀ (X : CData) (n₀ : ℕ) (C cε : ℝ), n₁ ≤ n₀ → 0 < cε → cε ≤ 1 / 90000 → X.HypC n₀ A C cb → X.FinVol →
      GeoC X Cres cε Cv Cd Cq →
      ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
        X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ 1 Mod ∧
        X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (1 + 1) Mod := by
  obtain ⟨cp, hcp, hprob⟩ := cn_prob
  obtain ⟨cb, cn, hcb, hcn, hnear⟩ := cn_near
  refine ⟨min cp cn, cb, lt_min hcp hcn, hcb, fun Cd Cq hCd hCq hCC => ?_⟩
  obtain ⟨C₁, hC₁, hdeep⟩ := cnd_far_deep Cd Cq hCd hCq hCC
  refine ⟨C₁, hC₁, fun Cv Cres A hCv hA => ?_⟩
  obtain ⟨np, hprob⟩ := hprob Cv Cres hCv
  obtain ⟨nn, hnear⟩ := hnear Cv Cres A C₁ hCv hA hC₁
  refine ⟨max (max np nn) 1, fun X n₀ C cε hn hcε hcε2 hXC hV hG => ?_⟩
  obtain ⟨hR, S, volK, hS, hD, hK, hNL, hPk, hDp⟩ := hG
  have hN := S.nearCount_of_layers (by positivity) hNL
  have hX := hXC.1
  have hn₀ : 1 ≤ n₀ := le_trans (le_max_right _ _) hn
  have hnX : n₀ ≤ X.I.n := hX.1.1
  have hn1 : 1 ≤ X.I.n := le_trans hn₀ hnX
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨hq, -⟩ := X.qq_spec hX
  by_cases hq0 : X.qq = 0
  · have hI0 : ∀ x, x ∈ S.I0 := fun x => by
      rcases hS.2.2.2.1 x with h | ⟨J, h1, h2, -⟩
      · exact h
      · omega
    have hε := (epsilon_small_bounds hcε (by linarith) hn1 (one_le_autInst_f X.I)).1
    have hd : ∀ x γ v, X.dist x γ v ≤ cn_eps X cε := fun x γ v => by
      unfold CData.dist
      rw [cartan_distance_eq_zero_of_definite (by have := hq v; unfold q0At AutInst.pAt AutInst.qAt at this; rw [hq0] at this; exact this)]
      exact hε.le
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_, ?_, cnd_deep_zero X (by norm_num)⟩
    · unfold CData.ProbMod
      rw [X.vol_eq]
      have h1 := Real.exp_pos (-(min cp cn * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)))
      have h2 : 0 ≤ X.μ.real Set.univ := measureReal_nonneg
      nlinarith
    · unfold CData.NearStep
      have hz : ∀ x, X.nearS (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) x = 0 := fun x => by
        have := cn_nearS_le X hX (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) x 0 fun T hT => by
          have : T = ∅ := Finset.eq_empty_of_forall_notMem fun γ hγ =>
            (hT γ hγ).2 (hN.1 x (hI0 x) γ (hT γ hγ).1.1 (hT γ hγ).1.2)
          simp [this]
        simpa using this
      simp [hz]
    · refine cnd_far_zero X C₁ hn1 hq0 Set.univ fun x _ γ hne => ?_
      by_contra hγ
      exact hne (hN.1 x (hI0 x) γ hγ (hd x γ))
  · have hq1 : 1 ≤ X.qq := Nat.one_le_iff_ne_zero.2 hq0
    have hY := cnd_two_le_Y X hn₀ hX
    obtain ⟨hfar, hdp⟩ := hdeep C₁ le_rfl X S volK n₀ A hn₀ hX hq1 hV hS hPk (hDp hq1)
    refine ⟨S.Mod C₁, S.measurableSet_Mod hS C₁, ?_, ?_, hfar, hdp _ (by norm_num)⟩
    · exact cn_probMod_mono X (min_le_left _ _) (hprob X S n₀ A C₁
        (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) hnX) hX (cnd_tauS_le_half X hC₁ hq1 hY) hV hS hD
        hK hR)
    · exact cn_nearStep_mono X (X.Ds_nonneg hp) (min_le_right _ _) (hnear X S n₀ C cε
        (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) hnX) hn₀ hXC hq1 hcε hcε2 hS hD hK hR hN)

def StepsG (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.OpExists ∧ X.KernelDiag ∧ X.FinVol ∧ X.LowProj ∧ GeoS X cε Cv Cd Cq

def StepsG'' (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.RegRep ∧ X.KernelDiag ∧ X.FinVol ∧ GeoS X cε Cv Cd Cq

theorem cusp_facts_of_geometry : ∃ c₁ cb : ℝ, 0 < c₁ ∧ 0 < cb ∧ ∀ Cd Cq : ℝ, 1 ≤ Cd → 0 ≤ Cq → 16 * Cq ≤ Cd → ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ Cv Cres A : ℝ, 1 ≤ Cv → 1 ≤ A → ∃ n₁ : ℕ, ∀ (n₀ : ℕ) (C cε : ℝ), n₁ ≤ n₀ → 0 < cε → cε ≤ 1 / 90000 →
      (∀ X : CData, cn_ResBound X Cres) →
      (StepsG n₀ A C cb cε Cv Cd Cq → StepsC' n₀ A C cb c₁ 1 cε C₁) ∧
      (StepsG'' n₀ A C cb cε Cv Cd Cq → StepsC'' n₀ A C cb c₁ 1 cε C₁) := by
  obtain ⟨c₁, cb, hc₁, hcb, h⟩ := cn_mod
  refine ⟨c₁, cb, hc₁, hcb, fun Cd Cq hCd hCq hCC => ?_⟩
  obtain ⟨C₁, hC₁, h⟩ := h Cd Cq hCd hCq hCC
  refine ⟨C₁, hC₁, fun Cv Cres A hCv hA => ?_⟩
  obtain ⟨n₁, h⟩ := h Cv Cres A hCv hA
  refine ⟨n₁, fun n₀ C cε hn hcε hcε2 hR => ⟨fun hS X hX => ?_, fun hS X hX => ?_⟩⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := hS X hX
    exact ⟨s1, s2, s3, s4, h X n₀ C cε hn hcε hcε2 hX s3 ⟨hR X, s5⟩⟩
  · obtain ⟨s1, s2, s3, s5⟩ := hS X hX
    exact ⟨s1, s2, s3, h X n₀ C cε hn hcε hcε2 hX s3 ⟨hR X, s5⟩⟩

def UniformGeometricFacts : Prop :=
  ∃ cε Cv Cd Cq : ℝ, 0 < cε ∧ cε ≤ 1 / 90000 ∧ 1 ≤ Cv ∧ 1 ≤ Cd ∧ 0 ≤ Cq ∧ 16 * Cq ≤ Cd ∧ ∀ cb Cres A Cb : ℝ, 0 < cb → 1 ≤ A →
    ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ n₀' ≥ n₀, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7,
      (ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀' A Cb →
        StepsG n₀' A C cb cε Cv Cd Cq

theorem theorem_count_of_geometry : ∃ c' cb : ℝ, 0 < c' ∧ 0 < cb ∧ ∀ Cd Cq Cv Cres A Cb cε : ℝ, 1 ≤ Cd → 0 ≤ Cq → 16 * Cq ≤ Cd → 1 ≤ Cv → 1 ≤ A → 0 < cε → cε ≤ 1 / 90000 →
    ∃ (n₁ : ℕ) (C₂ : ℝ), ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C : ℝ), n₁ ≤ n₀ → C₂ ≤ C → adm2 D → adm7 D Cres → DiscreteSeriesDecayBound D →
      Conclusion2 D n₀ A Cb → StepsG'' n₀ A C cb cε Cv Cd Cq → PointsLemma D n₀ A C c' cb := by
  obtain ⟨c₁, cb, hc₁, hcb, h⟩ := cusp_facts_of_geometry
  obtain ⟨c', hc', n₃, hfin⟩ := third_part_of_estimates c₁ (1 + 1) hc₁ (by norm_num)
  refine ⟨c', cb, hc', hcb, fun Cd Cq Cv Cres A Cb cε hCd hCq hCC hCv hA hcε hcε2 => ?_⟩
  obtain ⟨C₁, hC₁, h⟩ := h Cd Cq hCd hCq hCC
  obtain ⟨n₁, h⟩ := h Cv Cres A hCv hA
  obtain ⟨C₃, h3⟩ := StepsC'_of_last
  obtain ⟨C₀, hR⟩ := StepsC_of_refined cε C₁ c₁ A 1 hcε (by linarith) hC₁ hc₁ hA (by norm_num)
  obtain ⟨C₄, hfin⟩ := hfin Cb
  refine ⟨max (max n₁ n₃) 1, max (max C₃ C₀) C₄, fun D n₀ C hn hC h2 h7 hdec hb hS => ?_⟩
  have hn1 : n₁ ≤ n₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn3 : n₃ ≤ n₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : 1 ≤ n₀ := le_trans (le_max_right _ _) hn
  have hC3 : C₃ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC0 : C₀ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC4 : C₄ ≤ C := le_trans (le_max_right _ _) hC
  have s2 := (h n₀ C cε hn1 hcε hcε2 (residue_bound_of_admitted D Cres h7)).2 hS
  have s1 := h3 D n₀ A Cb C cb c₁ 1 cε C₁ hn0 hC3 h2 hb s2
  exact hfin D n₀ A C cb hn3 hC4 hb (hR D n₀ C cb hn0 hC0 hdec s1)

end Formalism.MainNotions.LeviCoordinates

end
