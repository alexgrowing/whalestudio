import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointMapLinearity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section
namespace GlobalTheory.ChainTw.UnifFree

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem mu_ratio (t t' : T) (i j : ℕ) :
    (comR R t).μ i * ((comR R t).μ j)⁻¹ = (comR R t').μ i * ((comR R t').μ j)⁻¹ := by
  show R.mu0 i * R.xi t * (R.mu0 j * R.xi t)⁻¹ = R.mu0 i * R.xi t' * (R.mu0 j * R.xi t')⁻¹
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_right_eq_div, mul_div_mul_right_eq_div]

theorem isHval_tuple {t t' : T} {S : Set (HeightOneSpectrum (𝓞 D.host.F))} {k : ℕ} {H : ℂ}
    (h : IsHval (comR R t) S k H) : IsHval (comR R t') S k H := by
  obtain ⟨Λ, h1, h2⟩ := h
  refine ⟨Λ, fun i hi => ⟨(h1 i hi).1, fun z hz => ?_⟩, h2⟩
  rw [(h1 i hi).2 z hz, mu_ratio R t t' i (k + 1)]

theorem ipTh_self {V W : HSp D} (m : Measure (WO V W)) (X : Set (WO V W)) (f : WO V W → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = ((nrm2 m X f : ℝ) : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  show f w * (starRingEnd ℂ) (f w) = _
  rw [Complex.mul_conj']
  push_cast
  ring

theorem unifY (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) (k : ℕ) (hk : k + 1 < D.R.m) :
    ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
      IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v := by
  have hk' : k < D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) k (stY R t k) := fun t => (hC t).2.1 k hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (k + 1) (stY R t (k + 1)) := fun t => (hC t).2.1 (k + 1) hk
  have hp : ∀ t, IsStep (twR R t) (k + 1) (stepY R t k) := fun t => (hC t).2.2.2.1 k hk
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D k) (Yc D (k + 1))
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM k hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D k) (Yc D (k + 1)) (GlobalTheory.Chain.expS D ⟨k, hk'⟩) (GlobalTheory.Chain.expT D ⟨k, hk'⟩) (R.ωY t k) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) k hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vY t k) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _ (R.ωY t k) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D k)), zReal (stepY R t k) m X φ v g * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      zReal (stepY R A.μ0 k) m X φ v g * (nrm2 m X (R.vY t k) : ℂ) := fun t g => by
    have e : coefW (stepY R t k).ω m X ((stepY R t k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
        coefW (stepY R A.μ0 k).ω m X ((stepY R A.μ0 k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY t k) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨k, hk'⟩ _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ (R.ωY t k) (R.ωY A.μ0 k)
        (R.vY t k) (R.vY A.μ0 k) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepY R t k) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vY t k) : ℝ) : ℂ) / (nrm2 m X (R.vY A.μ0 k) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepY R t k) m X φ v g ∂mR) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * (nrm2 m X (R.vY t k) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY A.μ0 k) : ℝ) : ℂ) (fun g => zReal (stepY R t k) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY t k) : ℝ) : ℂ) (fun g => zReal (stepY R A.μ0 k) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY A.μ0 (k + 1)) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) * ∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast ((hV A.μ0).1 (k + 1) hk).2.ne'
  · obtain ⟨hv1, hv2⟩ := (hV t).1 (k + 1) hk
    have hPi : (∏ PP ∈ R.Q t, idxQ PP (k + 1)) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).1 k hk m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP (k + 1)) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepY R t k) m X φ v g ∂mR) =
        (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY t (k + 1)) / ∏ PP ∈ R.Q t, idxQ PP (k + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) *
        ((∫ g, zReal (stepY R t k) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ)) = _
    rw [hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem unifX (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) :
    ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
      IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ)
        fun _ => v := by
  have h2 := D.R.two_le_m
  have hk' : D.R.m - 1 < D.R.m := by omega
  have e1 : D.R.m - 1 + 1 = D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1) (stY R t (D.R.m - 1)) := fun t => (hC t).2.1 _ hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1 + 1) (stX R t) := fun t => by
    rw [e1]; exact (hC t).2.2.1
  have hp : ∀ t, IsStep (twR R t) (D.R.m - 1 + 1) (stepX R h t) := fun t => by
    rw [e1]; exact (hC t).2.2.2.2
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D (D.R.m - 1)) D.sp.X'
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM _ hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D (D.R.m - 1)) D.sp.X' (GlobalTheory.Chain.expS D ⟨D.R.m - 1, hk'⟩)
      (GlobalTheory.Chain.expT D ⟨D.R.m - 1, hk'⟩) (R.ωX t) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) _ hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vX t) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ _ _ (R.ωX t) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D (D.R.m - 1))), zReal (stepX R h t) m X φ v g * (nrm2 m X (R.vX A.μ0) : ℂ) =
      zReal (stepX R h A.μ0) m X φ v g * (nrm2 m X (R.vX t) : ℂ) := fun t g => by
    have e : coefW (stepX R h t).ω m X ((stepX R h t).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX A.μ0) : ℂ) =
        coefW (stepX R h A.μ0).ω m X ((stepX R h A.μ0).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX t) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨D.R.m - 1, hk'⟩ _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ (R.ωX t)
        (R.ωX A.μ0) (R.vX t) (R.vX A.μ0) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepX R h t) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vX t) : ℝ) : ℂ) / (nrm2 m X (R.vX A.μ0) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepX R h t) m X φ v g ∂mR) * (nrm2 m X (R.vX A.μ0) : ℂ) =
      (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * (nrm2 m X (R.vX t) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX A.μ0) : ℝ) : ℂ) (fun g => zReal (stepX R h t) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX t) : ℝ) : ℂ) (fun g => zReal (stepX R h A.μ0) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) * ∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast (hV A.μ0).2.2.ne'
  · have hv1 := (hV t).2.1
    have hv2 := (hV t).2.2
    have hPi : (∏ PP ∈ R.Q t, idxQ PP D.R.m) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).2 m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP D.R.m) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepX R h t) m X φ v g ∂mR) =
        (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP D.R.m : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) / ∏ PP ∈ R.Q t, idxQ PP (D.R.m - 1 + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) *
        ((∫ g, zReal (stepX R h t) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (D.R.m - 1 + 1) : ℝ) : ℂ)) = _
    rw [e1, hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem rUnif_of : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → RealZetaQ D → Restore D → ∀ h : RangeX R, RChain R h → RMeas R → RVol R → RNrm R → RUnif R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hF hG hZ hRs h hC hM hV hN
  exact ⟨fun k hk => unifY R hF.core.lev hG hZ hRs h hC hM hV hN k hk, unifX R hF.core.lev hG hZ hRs h hC hM hV hN⟩

end GlobalTheory.ChainTw.UnifFree
