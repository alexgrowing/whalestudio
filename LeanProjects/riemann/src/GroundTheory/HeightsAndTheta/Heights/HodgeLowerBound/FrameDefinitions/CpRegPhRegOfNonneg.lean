import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Ties

variable {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}

structure LogLogRegularisationSetting.IsTied {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A) : Prop where
  e1_tendsto_zero : Tendsto S.e1 (𝓝[>] 0) (𝓝 0)
  K_tendsto : Tendsto S.K (𝓝[>] 0) atTop
  K_ge : ∀ᶠ t in 𝓝[>] 0, S.R.Clog * Real.log (Real.log t⁻¹) ≤ S.K t
  compare : ∀ᶠ t in 𝓝[>] 0, ∀ j k : Fin S.R.N, ∀ x ∈ S.R.mid j ∩ S.R.mid k,
    |S.R.phReg S.ρ (S.K t) t j x - S.R.phReg S.ρ (S.K t) t k x| ≤ S.e1 t

structure BoundedRegularisationSetting.IsTied {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ} (S : BoundedRegularisationSetting M Xo a w) : Prop where
  e1_tendsto_zero : Tendsto S.e1 (𝓝[>] 0) (𝓝 0)
  compare : ∀ᶠ t in 𝓝[>] 0, ∀ j k : Fin S.B.N, ∀ x ∈ S.B.mid j ∩ S.B.mid k,
    |S.B.phReg S.ρ t j x - S.B.phReg S.ρ t k x| ≤ S.e1 t

end Ties

open Classical in

def smoothRepConj (P : Ideal (MRing ι)) (A : HermLine ι) : HermLine ι :=
  if h : ∃ A' : HermLine ι, A'.a = A.a ∧ IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ ∀ z ∈ mcPts P, A'.h z = A.h z then
    h.choose
  else smoothRep P A

theorem smoothRepConj_h {P : Ideal (MRing ι)} (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    (smoothRepConj P A).h z = A.h z := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.2.2 z hz
  · exact smoothRep_h A hz

theorem smoothRepConj_a (P : Ideal (MRing ι)) (A : HermLine ι) : (smoothRepConj P A).a = A.a := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.1
  · exact smoothRep_a P A

theorem smoothRepConj_conj {P : Ideal (MRing ι)} (A : HermLine ι)
    (h : ∃ A' : HermLine ι, A'.a = A.a ∧ IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ ∀ z ∈ mcPts P, A'.h z = A.h z) :
    IsConjInvariantH (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  rw [dif_pos h]
  exact h.choose_spec.2.2.1

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

section Numbers

variable (H : HodgeData D)

def cuspCorr {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu H z + Cd.cuspWeight z / 2

variable {w : ((Σ k, ι k) → ℂ) → ℝ}

def MUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : HermLine ι :=
  smoothRepConj (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.bregWeight t' (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def topMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => MUc H S B p q t') / (q : ℝ) ^ (D.n + 1)

def geomDegMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : ℝ :=
  geomDeg (mCoordIdeal D.y) (MUc H S B p q t') D.n / (q : ℝ) ^ D.n

def htMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) (W : Ideal (MRing ι)) : ℝ :=
  II K ι W 1 ![MUc H S B p q t'] / ((q : ℝ) * degC W)

end Numbers

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem cpReg_trunc_of_nonneg {K : ℝ} (hK : 0 ≤ K) (j : Fin cpReg.N) : cpReg.trunc K j = fun _ => 0 := by
  funext y
  have hc : (fun y => max (cpReg.u j y) (-K)) = fun _ => (0 : ℝ) :=
    funext fun y => by
      simp only [RegChartData.u, GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, cpReg, cpCharts]
      simp [hK]
  unfold RegChartData.trunc ReciprocityTheory.AnForm.A.limsupExt
  rw [hc]
  split_ifs
  · exact limsup_zero_real _
  · rfl

theorem cpReg_phReg_of_nonneg (ρ : ReciprocityTheory.AnForm.A.Mollifier 1) {K : ℝ} (hK : 0 ≤ K) (t : ℝ) (j : Fin cpReg.N)
    (x : CP 1) : cpReg.phReg ρ K t j x = 0 := by
  simp only [RegChartData.phReg, RegChartData.smoothed, ReciprocityTheory.AnForm.A.molli]
  rw [cpReg_trunc_of_nonneg hK]
  simp [cpReg, cpCharts]

def lineRegT : LogLogRegularisationSetting lineModel (lineData II hII).Xo (muLine (lineHodge II hII)) :=
  { lineReg II hII with K := fun t => t⁻¹ }

theorem lineRegT_tied : (lineRegT II hII).IsTied where
  e1_tendsto_zero := tendsto_id.mono_left nhdsWithin_le_nhds
  K_tendsto := tendsto_inv_nhdsGT_zero
  K_ge := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    show cpReg.Clog * Real.log (Real.log t⁻¹) ≤ t⁻¹
    have : cpReg.Clog = 0 := rfl
    rw [this, zero_mul]
    exact inv_nonneg.2 (le_of_lt ht)
  compare := by
    filter_upwards [self_mem_nhdsWithin] with t ht j k x _
    have h0 : ∀ (j' : Fin (lineRegT II hII).R.N) (x' : lineModel.Xc),
        (lineRegT II hII).R.phReg (lineRegT II hII).ρ ((lineRegT II hII).K t) t j' x' = 0 :=
      fun j' x' => cpReg_phReg_of_nonneg _ (inv_nonneg.2 (le_of_lt ht)) t j' x'
    rw [h0, h0, sub_zero, abs_zero]
    exact le_of_lt ht

def lineBRegC : BoundedRegularisationSetting lineModel (lineData II hII).Xo
    (lineHodge II hII).aMu (cuspCorr (lineHodge II hII) (gaussCusp II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    show (0 : ℝ) = _
    rw [cuspCorr, phMu_line (mem_mcPts_line.1 hz.2), cuspWeight_gauss, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

theorem lineBRegC_tied : (lineBRegC II hII).IsTied where
  e1_tendsto_zero := tendsto_id.mono_left nhdsWithin_le_nhds
  compare := by
    filter_upwards [self_mem_nhdsWithin] with t ht j k x _
    have h0 : ∀ (j' : Fin (lineBRegC II hII).B.N) (x' : lineModel.Xc),
        (lineBRegC II hII).B.phReg (lineBRegC II hII).ρ t j' x' = 0 :=
      fun j' x' => cpBounded_phReg _ t j' x'
    rw [h0, h0, sub_zero, abs_zero]
    exact le_of_lt ht

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
