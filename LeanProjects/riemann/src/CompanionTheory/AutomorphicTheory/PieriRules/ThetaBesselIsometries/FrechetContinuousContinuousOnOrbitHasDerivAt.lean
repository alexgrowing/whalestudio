import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWDeriv

open Filter Topology PI.UpqRep
open scoped ContDiff

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_continuousOn {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : ContinuousOn f (Formalism.QuantumDeterminants.UH H) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have h1 : ContinuousWithinAt F (Formalism.QuantumDeterminants.UH H) g :=
    (hF.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (hfF g hgU hg)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with x hx hx'
  exact hfF x hx hx'

theorem left_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hg : g ∈ U) (hgH : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, inUH H x → f x = F x) (hX : AAInvW.inLH H X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  have hγ1 := Formalism.REAL.hasDerivAt_mul_exp_smul_zero 1 X
  simp only [Matrix.one_mul] at hγ1
  have hγ : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 :=
    (Formalism.REAL.mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ1
  have hγ0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g))
      (fderiv ℝ F g (X * g)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) * g ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (AAInvW.ana_mul (AAInvW.ana_expt hH hX t) hgH)

theorem left_smooth {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : AAInvW.inLH H X)
    (hf' : ∀ g, inUH H g → ∀ D, HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) D 0 → D = f' g) :
    SmoothOnH H f' ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (f' g) 0 := by
  constructor
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
    refine ⟨U, fun k => fderiv ℝ F k (X * k), hU, hg₀U, ?_, ?_⟩
    · have h1 := hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty
      have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => X * k) U :=
        (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)).contDiff.contDiffOn
      exact h1.clm_apply h2
    · intro k hk hkH
      exact (hf' k hkH _ (left_hasDerivAt hH hU hk hkH hF hfF hX)).symm
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
    have h := left_hasDerivAt hH hU hgU hg hF hfF hX
    rwa [hf' g hg _ h] at h

end Smooth

section Rep

variable {k r : ℕ}

def DerFacts (R : Rep k r) : Prop :=
  ∀ X, InLieHpk k r X →
    (∀ v ∈ R.sm, dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧
      HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) R.σ X v) 0) ∧
    ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) R.σ X w⟫_ℂ

theorem hInvol (k r : ℕ) : AAInvW.HInvol (Hpk k r) :=
  ⟨Formalism.QuantumDeterminants.GBasic.Hpk_herm k r, Formalism.QuantumDeterminants.GBasic.Hpk_sq k r⟩

theorem dsigW_mem {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ u ∈ R.sm, dsigW (k := k) (r := r) R.σ W u ∈ R.sm := by
  induction W with
  | nil => intro u hu; exact hu
  | cons X W ih =>
    intro u hu
    exact ((hD X (hW X (by simp))).1 _ (ih (fun Y hY => hW Y (by simp [hY])) u hu)).1

theorem dsigW_append {R : Rep k r} (W : List (Mx k r)) (Y : Mx k r) (u : R.H) :
    dsigW (k := k) (r := r) R.σ (W ++ [Y]) u =
      dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y u) := by
  induction W with
  | nil => rfl
  | cons X W ih => simp only [List.cons_append, dsigW, ih]

theorem dsigW_adjoint {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ w ∈ R.sm, ∃ w' : R.H, ∀ u ∈ R.sm, ⟪w, dsigW (k := k) (r := r) R.σ W u⟫_ℂ = ⟪w', u⟫_ℂ := by
  induction W with
  | nil => intro w _; exact ⟨w, fun u _ => rfl⟩
  | cons X W ih =>
    intro w hw
    have hX := hD X (hW X (by simp))
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (by simp [hY])
    obtain ⟨w', hw'⟩ := ih hW' _ (hX.1 w hw).1
    refine ⟨-w', fun u hu => ?_⟩
    have h := hX.2 w hw _ (dsigW_mem hD W hW' u hu)
    rw [hw' u hu] at h
    rw [inner_neg_left, h, neg_neg]
    rfl

theorem eq_zero_of_closure {R : Rep k r} {x : R.H} (hx : x ∈ closure R.sm) (h : ∀ w ∈ R.sm, ⟪w, x⟫_ℂ = 0) :
    x = 0 := by
  have hc : IsClosed {w : R.H | ⟪w, x⟫_ℂ = 0} := isClosed_eq (by fun_prop) continuous_const
  exact inner_self_eq_zero.mp (closure_minimal (t := {w : R.H | ⟪w, x⟫_ℂ = 0}) h hc hx)

theorem sm_comb {R : Rep k r} (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    a • (x - y) - z ∈ R.sm :=
  R.smSub.sub_mem (R.smSub.smul_mem a (R.smSub.sub_mem hx hy)) hz

theorem dsigW_comb {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • (x - y) - z) =
      a • (dsigW (k := k) (r := r) R.σ W x - dsigW (k := k) (r := r) R.σ W y) - dsigW (k := k) (r := r) R.σ W z := by
  rw [← sub_eq_zero]
  have hm := dsigW_mem hD W hW
  refine eq_zero_of_closure (subset_closure
    (R.smSub.sub_mem (hm _ (sm_comb a hx hy hz)) (sm_comb a (hm _ hx) (hm _ hy) (hm _ hz)))) ?_
  intro w hw
  obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
  simp only [inner_sub_right, inner_smul_right, hw' _ (sm_comb a hx hy hz), hw' _ hx, hw' _ hy, hw' _ hz,
    sub_self]

theorem dsigW_deriv_eq {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {c : ℝ → R.H} {c' D : R.H} (hc : ∀ t, c t ∈ R.sm) (hc' : c' ∈ R.sm) (hd : HasDerivAt c c' 0)
    (hD' : HasDerivAt (fun t => dsigW (k := k) (r := r) R.σ W (c t)) D 0) :
    D = dsigW (k := k) (r := r) R.σ W c' := by
  rw [← sub_eq_zero]
  have hm := dsigW_mem hD W hW
  refine eq_zero_of_closure ?_ ?_
  · have h1 := (hasDerivAt_iff_tendsto_slope.mp hD').sub_const (dsigW (k := k) (r := r) R.σ W c')
    refine mem_closure_of_tendsto h1 (Eventually.of_forall fun t => ?_)
    have := sm_comb (((t - 0)⁻¹ : ℝ) : ℂ) (hm _ (hc t)) (hm _ (hc 0)) (hm _ hc')
    rw [Complex.coe_smul] at this
    exact this
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    have h1 : HasDerivAt (fun t => ⟪w, dsigW (k := k) (r := r) R.σ W (c t)⟫_ℂ) ⟪w, D⟫_ℂ 0 :=
      ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD'
    have h2 : HasDerivAt (fun t => ⟪w', c t⟫_ℂ) ⟪w', c'⟫_ℂ 0 :=
      ((innerSL ℂ w').restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simp only [hw' _ (hc _)] at h1
    rw [inner_sub_right, h1.unique h2, hw' _ hc', sub_self]

theorem dsigW_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X)
    (hs : SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)))
    (Y : Mx k r) (hY : InLieHpk k r Y) :
    SmoothOnH (Hpk k r)
        (fun g => dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) ∧
      ∀ g, inUH (Hpk k r) g → HasDerivAt
        (fun t : ℝ => dsigW (k := k) (r := r) R.σ W (R.σ (NormedSpace.exp ((t : ℂ) • Y) * g) v))
        (dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) 0 := by
  refine left_smooth (hInvol k r) hs hY ?_
  intro g hg D hDer
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • Y) ∈ UH (Hpk k r) :=
    fun t => AAInvW.ana_expt (hInvol k r) hY t
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2
  have hgv := hsm v hv g hg
  have e : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • Y) * g) v = R.σ (NormedSpace.exp ((t : ℂ) • Y)) (R.σ g v) := by
    intro t
    rw [PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication k r ε mu R.H R.σ hR.2 _ (hexp t) g hg]
    rfl
  simp only [e] at hDer
  exact dsigW_deriv_eq hD W hW (fun t => hsm _ hgv _ (hexp t)) ((hD Y hY).1 _ hgv).1 ((hD Y hY).1 _ hgv).2 hDer

theorem dsigW_orbit_smooth {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) :
    SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)) := by
  induction W using List.reverseRecOn with
  | nil => exact hv
  | append_singleton W Y ih =>
    have hW' : ∀ X ∈ W, InLieHpk k r X := fun X hX => hW X (by simp [hX])
    simp only [dsigW_append]
    exact (dsigW_orbit hR hD hv W hW' (ih hW') Y (hW Y (by simp))).1

theorem cw_tendsto {R : Rep k r} {V : Type} [NormedAddCommGroup V] {Bm : R.H → V}
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {α : Type} {l : Filter α} {u : α → R.H}
    (hu : ∀ᶠ a in l, u a ∈ R.sm)
    (h : ∀ W : List (Mx k r), (∀ X ∈ W, InLieHpk k r X) →
      Tendsto (fun a => dsigW (k := k) (r := r) R.σ W (u a)) l (𝓝 0)) :
    Tendsto (fun a => Bm (u a)) l (𝓝 0) := by
  obtain ⟨C, Ws, hWs, hb⟩ := hB
  have h1 : Tendsto (fun a => (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w (u a)‖).sum) l
      (𝓝 (Ws.map fun _ => (0 : ℝ)).sum) :=
    tendsto_list_sum Ws (fun w hw => by simpa using (h w (hWs w hw)).norm)
  have h2 := h1.const_mul C
  simp only [List.map_const', List.sum_replicate, smul_zero, mul_zero] at h2
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [hu] with a ha
  exact hb _ ha

theorem lin_comb {R : Rep k r} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Bm : R.H → V}
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    Bm (a • (x - y) - z) = a • (Bm x - Bm y) - Bm z := by
  have hsub : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v - w) = Bm v - Bm w := by
    intro v hv w hw
    have := ha _ (R.smSub.sub_mem hv hw) w hw
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub _ (R.smSub.smul_mem a (R.smSub.sub_mem hx hy)) _ hz, hs a _ (R.smSub.sub_mem hx hy), hsub _ hx _ hy]

end Rep

end GlobalTheory.CWDeriv

namespace GlobalTheory

open Filter Topology CWDeriv

theorem cwCont_continuousOn_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  intro hK k r ε mu R hR V _ _ Bm ha hs hB v hv
  have hD : DerFacts R := fun X hX =>
    ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).2.2.2.2⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  constructor
  · intro g hg
    have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
      (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
      (by
        intro W hW
        have h2 := (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
        have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
          have h := dsigW_comb hD W hW 0 h0 h0 h0
          simp only [zero_smul, zero_sub, neg_zero] at h
          rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
          simpa using h
        rw [← tendsto_sub_nhds_zero_iff] at h2
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
    refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]
  · intro X hX
    have hexp : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ R.sm :=
      fun t => hsm _ (AAInvW.ana_expt (hInvol k r) hX t)
    have hd := ((hD X hX).1 v hv).1
    have h1 := cw_tendsto hB (l := 𝓝[≠] (0 : ℝ))
      (u := fun t : ℝ => (((t - 0)⁻¹ : ℝ) : ℂ) • (R.σ (NormedSpace.exp ((t : ℂ) • X)) v -
        R.σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) v) - PI.UpqRep.dsig (k := k) (r := r) R.σ X v)
      (Eventually.of_forall fun t => sm_comb _ (hexp t) (hexp 0) hd)
      (by
        intro W hW
        have h2 := (dsigW_orbit hR hD hv W hW (dsigW_orbit_smooth hR hD hv W hW) X hX).2 1
          (by simp [PI.UpqRep.inUH])
        simp only [Matrix.mul_one] at h2
        have h3 := dsigW_deriv_eq hD W hW hexp hd ((hD X hX).1 v hv).2 h2
        rw [h3, hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff] at h2
        refine h2.congr fun t => ?_
        rw [dsigW_comb hD W hW _ (hexp t) (hexp 0) hd, Complex.coe_smul]
        rfl)
    rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff]
    refine h1.congr fun t => ?_
    rw [lin_comb ha hs _ (hexp t) (hexp 0) hd, Complex.coe_smul]
    rfl

end GlobalTheory

end
