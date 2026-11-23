import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurD
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SmoothIrredBK
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalAmpRoot
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalBetaInf

set_option linter.dupNamespace false

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDD.BM

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDD

def AmpDD : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlace L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - b → Integrable (pairMaj γ b) ν →
    ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v' ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

def AmpKF : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end Formalism.MainNotions.S.Pv.AmpDD.BM

namespace Formalism.MainNotions.S.Pv.AmpDDPf.BM

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf

theorem ampDD_thm : Formalism.MainNotions.S.Pv.AmpDD.BM.AmpDD := by
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := right_stabilizer_invariance
  intro hIn k r L h μG w0 l l' hOP γ μR νR ν hCD b hb hab' hpm v hv v' hv' ξ ξ'
  obtain ⟨hgap, hOK, -, hw0, hμG, hl, hl'⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay L.σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hw0DD : w0 ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0 := by
    have := Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 (Formalism.FourierDecayAlt.P.S3dx6.one_mem_uh (k := k) (r := r))
    rwa [(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ).1, ContinuousLinearMap.one_apply] at this
  obtain ⟨C1, hC1⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v' hv'
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by linarith
  have hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - Formalism.FourierDecayAlt.ThreeDimData.aOf r h)) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core L hμG hd hSch hNI hw1 l l' hl hl' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm hv hv' hC1 hC2 ξ ξ'

theorem amplitude_K_finite : Formalism.MainNotions.S.Pv.AmpDD.BM.AmpKF := by
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := right_stabilizer_invariance
  intro hIn k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf.BM

namespace Formalism.L2.SG.AmpOrbPf.BM

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

theorem ls_pair (hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) (hAt : CompanionTheory.Lime.BM.AtFormAdmOne)
    {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    ∃ (l : A.H → W.Wp) (l' : A.H → W.Wq),
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
        (psi D.R.k D.R.rS W.z (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π l ∧
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
        (psi D.R.k D.R.rS W.z' (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π' l' ∧
      Formalism.MainNotions.S.Pv.AmpDD.OnePlaceKF (toBessel D τ w w' θ W lam A hW hA hT hT') h W.μG
        (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) l l' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  obtain ⟨h1, h2⟩ := side_pair hW hA hT hT' hg hok
  obtain ⟨l, hl, hla, -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wp _ _ _ _ _ _ _ _ h1
  obtain ⟨l', hl', hla', -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wq _ _ _ _ _ _ _ _ h2
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hw0 := lowest_K_type_unit hA
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0),
      x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨l, l', hl, hl', ⟨⟨hg, hok, c_ne_zero D, hw0, hG, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inr hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inr hv)).2

theorem ampOrbNV (hJ : CompanionTheory.Lime.BM.UniqGap) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn) :
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  have hI := CompanionTheory.Lime.BM.inputs
  have hAt := CompanionTheory.Lime.BM.atFormAdmOne hJ
  have hNz := Formalism.MainNotions.S.Pv.AmpDDPf.nonzero_K_finite
  have hAKF := Formalism.MainNotions.S.Pv.AmpDDPf.BM.amplitude_K_finite
  have hCC := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  have hGap := fun h1 h2 => Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 Cn h1 h2
  intro hH hCl hCn τ w w' hTT θ W hW lam' hl A hA hT hT'
  obtain ⟨h, hg, hok, hcell⟩ := hGap hCl hCn hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0

  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp

  obtain ⟨v, hvK, hlv⟩ := hNz hKD hKS _ _ _ _ _ A.σ w0 W.Wp W.z L.c W.π hA.1 hA.2.1 hw0 l hl1 ⟨x, hx, hlx⟩
  obtain ⟨v', hvK', hlv'⟩ := hNz hKD hKS _ _ _ _ _ A.σ w0 W.Wq W.z' L.c W.π' hA.1 hA.2.1 hw0 l' hl1' ⟨x', hx', hlx'⟩

  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  set s : ℂ := ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ with hs
  have hs0 : s ≠ 0 := mul_ne_zero (inner_self_ne_zero.mpr hlv) (inner_self_ne_zero.mpr hlv')
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  refine ⟨fun g => (K1 * s⁻¹ * dg⁻¹) • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v') g,
    kfin_coef L _ v v' _ _ hvK hvK', ?_⟩
  intro γ hγ hGf hMono hRel μR νR ν hRH hOQ hqR
  have hCD : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨b, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD b hb0 hbm hbi v v' hvK hvK' (l v) (l' v')
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hJ2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      (s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := by
    have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := hAmp
    have e1 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        s⁻¹ • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e1, hAmp']
    exact smul_smul s⁻¹ dg⁻¹ _
  rw [hJ1, hJ2]
  have hO := orbInt_smul L (K1 * s⁻¹ * dg⁻¹) (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν
  have e2 : K1 • ((s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν) =
      (K1 * s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' (l v) (l' v')) γ ν := by
    rw [smul_smul]
    congr 1
    ring
  exact e2.trans hO.symm

theorem ampOrb0 (hJ : CompanionTheory.Lime.BM.UniqGap) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl) : Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 0 :=
  ampOrbNV hJ hKD D large₂ C' Cl Cg cb Cu cT CT C0 0 (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith))

end Formalism.L2.SG.AmpOrbPf.BM

namespace Formalism.L2.S.Pv.AmpOrbCoef.BM

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf Formalism.L2.S.Pv.AmpOrbCoef

theorem ampOrbCoefDD_of (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.MainNotions.S.Pv.LemmaJ.AmpOrbCoefDD := by
  intro Cg cb Cu cT CT C0
  refine ⟨0, 1000, fun C' Cl _ hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' => ?_⟩
  have hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs := CompanionTheory.Lime.BM.inputs
  have hAt := CompanionTheory.Lime.BM.atFormAdmOne hJ
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := by unfold l1dist; simp
  obtain ⟨h, hg, hok, hcell⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith) hH τ (lamD D τ) hl0
  set L := toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := Formalism.L2.SG.AmpOrbPf.BM.ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0

  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith) hH τ w w' hTT θ W hW (lamD D τ) hl0 A hA hT hT'
      w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp

  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  have hW' := hW
  obtain ⟨hc1, hc2, -, -, -, -, -, hUW, -, hUW', -, hNq, hq, hq'⟩ := hW'
  have hA' := hA
  obtain ⟨-, -, -, -, hv0s, hv0ne, -, hcN, hl2, hl2', -⟩ := hA'
  have hNa : ∀ᵐ x ∂W.μN, Matrix.of x ∈ Nset D.R.k D.R.rS := by
    rw [hNq]; exact Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN _
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have : SigmaFinite W.μN := by
    have := (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS _ hκ0 hκtop).1
    rw [hNq]; exact this
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hNt' : Nontrivial W.Wq := by obtain ⟨g, -, hU⟩ := hc2; exact hU.1
  obtain ⟨xb, hxb, hBx⟩ := B_ne hA.2.1 hG hUW hNa hq hv0s hcN hl2
  obtain ⟨xb', hxb', hBx'⟩ := B_ne hA.2.1 hG hUW' hNa hq' hv0s hcN hl2'
  have hc0ne : c0 ≠ 0 := by
    intro e; apply hBx; have h1 := hc0 xb hxb; rw [e] at h1; rw [h1]; exact zero_smul ℂ _
  have hc0ne' : c0' ≠ 0 := by
    intro e; apply hBx'; have h1 := hc0' xb' hxb'; rw [e] at h1; rw [h1]; exact zero_smul ℂ _

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have htne : t ≠ 0 := by rw [ht]; exact_mod_cast norm_ne_zero_iff.mpr hv0ne
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hv0s
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  set s : ℂ := ⟪l x, l x⟫_ℂ * ⟪l' x', l' x'⟫_ℂ with hs
  have hs0 : s ≠ 0 := mul_ne_zero (inner_self_ne_zero.mpr hlx) (inner_self_ne_zero.mpr hlx')
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    obtain ⟨-, -, hn1, -⟩ := hw0
    exact_mod_cast (fdegH_pos hA.1 hA.2.1 hG hn1).ne'
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK1ne : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero (by exact_mod_cast hcN.ne')) (mul_ne_zero hc0ne htne)) ?_
    exact (map_ne_zero _).2 (mul_ne_zero hc0ne' htne)
  refine ⟨x, x', l x, l' x', l x, l' x', K1 * s⁻¹ * dg⁻¹,
    mul_ne_zero (mul_ne_zero hK1ne (inv_ne_zero hs0)) (inv_ne_zero hdg0), hDDs x hx, hDDs x' hx',
    hOP.1.2.2.2.2.2.1 x hx x hx, hOP.1.2.2.2.2.2.2 x' hx' x' hx', inner_self_ne_zero.mpr hlx,
    inner_self_ne_zero.mpr hlx', ?_⟩
  intro γ hγ hGf hMono hRel μR νR ν hRH hOQ hqR
  have hCD : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨b, hb0, hbm, hbi⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD hMono
  have hAmp := Formalism.MainNotions.S.Pv.AmpDDPf.BM.ampDD_thm hI _ _ L h W.μG w0 l l' hOP.1 γ μR νR ν hCD b hb0 (by linarith) hbi
    x hx x' hx' (l x) (l' x')
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hJ2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      (s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := hAmp
    have e1 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        s⁻¹ • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e1, hAmp']
    exact smul_smul s⁻¹ dg⁻¹ _
  rw [hJ1, hJ2]
  have hO := orbInt_smul L (K1 * s⁻¹ * dg⁻¹) (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν
  have e2 : K1 • ((s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν) =
      (K1 * s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    rw [smul_smul]
    congr 1
    ring
  exact e2.trans hO.symm

theorem ampUnif_gap (hJ : CompanionTheory.Lime.BM.UniqGap) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.L2.S.Pv.AmpFinal.ampUnif_of_parts (fun Cg cb Cu cT CT C0 => ⟨0, 1000, fun C' Cl _ hCl D large₂ =>
            Formalism.L2.SG.AmpOrbPf.BM.ampOrb0 hJ hKD D large₂ C' Cl Cg cb Cu cT CT C0 hCl⟩)
    Formalism.MainNotions.S.Pv.LemmaJ.rootJac_holds Formalism.MainNotions.S.Pv.LemmaJ.rootHaar_holds Formalism.MainNotions.S.Pv.LemmaJ.exists_orbQuot₂
    Formalism.MainNotions.S.Pv.LemmaJ.relAtPt_holds
    (Formalism.MainNotions.S.Pv.LemmaJ.ampNZ_of_parts (ampOrbCoefDD_of hJ) Formalism.MainNotions.S.Pv.BetaCut.betaInfCoef_ne_zero)

end Formalism.L2.S.Pv.AmpOrbCoef.BM
