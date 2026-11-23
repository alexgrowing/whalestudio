import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpCuspIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem ComponentSetting.wSt_torusSmul (X : ComponentSetting D O Lt) (B p q : ℕ) (t t' : ℝ) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    X.wSt B p q t t' (torusSmul c z) = X.wSt B p q t t' z := by
  have ha : (X.MUq B p q t').a = (X.NbarQ B p q t).a := by
    simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
    rfl
  have hpos : 0 < ∏ k, ‖c k‖ ^ (X.NbarQ B p q t).a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := (X.MUq B p q t').smul c z hc
  have h2 := (X.NbarQ B p q t).smul c z hc
  rw [ha] at h1
  unfold ComponentSetting.wSt
  rw [e, h1, h2, Real.log_mul hpos.ne' ((X.MUq B p q t').pos z hz.1).ne',
    Real.log_mul hpos.ne' ((X.NbarQ B p q t).pos z hz.1).ne']
  ring

theorem StokesLimitTp.proof (hLim : TpIntegrandLimit.Statement) (hAbove : RegAboveWeight.Statement)
    (hU : TpCuspIntegrable.Statement) (hConv : PtsBddConv.Statement) (hMono : PtsMonoSemipos.Statement) :
    StokesLimitTp.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨t₁, ht₁, hL⟩ := hLim II Ψ K ι Ω E D O Lt X B p q hq
  obtain ⟨t₃, ht₃, N₂, hN₂, hA⟩ := hAbove II Ψ K ι Ω E D O Lt X
  refine ⟨min t₁ t₃, lt_min ht₁ ht₃, fun t ht0 ht hsp => ?_⟩
  obtain ⟨N₁, C, s₀, hs₀, hN₁, hbd, hpt⟩ := hL t ht0 (ht.trans (min_le_left _ _))
  obtain ⟨hint, hlim⟩ := hConv K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q (X.wSt B p q t)
    (fun z => cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))) N₁ C s₀
    D.arith hsp.1 hr hN₁ hs₀
    (fun s hs hs' => ⟨(hbd s hs hs').1, (hbd s hs hs').2, fun c hc z hz => X.wSt_torusSmul B p q t s c hc z hz⟩) hpt
  refine ⟨hlim, ?_⟩
  refine hMono K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q _ (fun z => X.Cd.cuspWeight z / 2) N₂ D.arith hsp hr
    hN₂ (fun z hz hzN => ?_) hint (hU II Ψ K ι Ω E D O Lt X B p q t hsp.1)
  have h := hA t ht0 (ht.trans (min_le_right _ _)) z hz hzN
  show phMu X.H z + X.Cd.cuspWeight z / 2 - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)) ≤
    X.Cd.cuspWeight z / 2
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
