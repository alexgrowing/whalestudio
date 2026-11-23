import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CuspIntertwiner

theorem exists_extend {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (e : ι → H) (f : ι → K)
    (he : Dense (Submodule.span ℂ (Set.range e) : Set H)) (c : ℂ) (h : ∀ i j, ⟪f i, f j⟫_ℂ = c * ⟪e i, e j⟫_ℂ) :
    ∃ A : H →L[ℂ] K, ∀ i, A (e i) = f i := by
  have hd : DenseRange (Finsupp.linearCombination ℂ e) := by
    rw [← Finsupp.range_linearCombination] at he
    exact he
  have hn : ∀ x : ι →₀ ℂ, ‖Finsupp.linearCombination ℂ f x‖ ≤ √‖c‖ * ‖Finsupp.linearCombination ℂ e x‖ := by
    intro x
    have h1 : ⟪Finsupp.linearCombination ℂ f x, Finsupp.linearCombination ℂ f x⟫_ℂ =
        c * ⟪Finsupp.linearCombination ℂ e x, Finsupp.linearCombination ℂ e x⟫_ℂ := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := congrArg norm h1
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at h2
    refine le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_)
    rw [h2, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  refine ⟨(Finsupp.linearCombination ℂ f).extendOfNorm (Finsupp.linearCombination ℂ e), fun i => ?_⟩
  have := LinearMap.extendOfNorm_eq hd ⟨_, hn⟩ (Finsupp.single i 1)
  simpa using this

theorem continuous_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) : Continuous t := by
  refine continuous_iff_continuousAt.2 fun y => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h1 : Continuous fun x => ‖t x - t y‖ := by
    simp only [@norm_eq_sqrt_re_inner ℂ, inner_sub_sub_self, h]
    fun_prop
  simpa using h1.tendsto y

theorem dense_span_tens {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H))
    {ι : Type} (s : ι → ∀ v, E v) (hs : DenseRange s) :
    Dense (Submodule.span ℂ (Set.range fun i => t (s i)) : Set H) := by
  have h1 : Submodule.span ℂ (Set.range t) ≤ (Submodule.span ℂ (Set.range fun i => t (s i))).topologicalClosure := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure (continuous_tens t h) (hs x) ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact dense_closure.1 (hd.mono h1)

theorem eq_of_inner_eq {X H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : X → H)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) {p q : H} (h : ∀ z, ⟪t z, p⟫_ℂ = ⟪t z, q⟫_ℂ) : p = q := by
  have h0 : innerSL ℂ (p - q) = 0 := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨z, rfl⟩
    rw [innerSL_apply_apply, ContinuousLinearMap.zero_apply, ← inner_conj_symm, inner_sub_right, h z, sub_self,
      map_zero]
  have := congrArg (fun L : H →L[ℂ] ℂ => L (p - q)) h0
  simp only [innerSL_apply_apply, ContinuousLinearMap.zero_apply, inner_self_eq_zero] at this
  exact sub_eq_zero.1 this

theorem inner_update {κ H : Type} [Fintype κ] [DecidableEq κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (z x : ∀ v, E v) (i : κ) (a : E i) :
    ⟪t z, t (Function.update x i a)⟫_ℂ = ⟪z i, a⟫_ℂ * ∏ v ∈ Finset.univ.erase i, ⟪z v, x v⟫_ℂ := by
  rw [h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

def tensML {κ H : Type} [Fintype κ] {E : κ → Type} [∀ v, NormedAddCommGroup (E v)]
    [∀ v, InnerProductSpace ℂ (E v)] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : (∀ v, E v) → H)
    (h : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hd : Dense (Submodule.span ℂ (Set.range t) : Set H)) :
    ContinuousMultilinearMap ℂ E H where
  toFun := t
  map_update_add' x i a b := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_add_right, inner_update t h, inner_update t h, inner_update t h, inner_add_right, add_mul]
  map_update_smul' x i c a := by
    refine (eq_of_inner_eq t hd fun z => ?_)
    rw [inner_smul_right, inner_update t h, inner_update t h, inner_smul_right, mul_assoc]
  cont := continuous_tens t h

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem denseRange_vec (M : DSModel V S) : DenseRange fun (u : M.Vec) (τ : D.what₂.Tau) => (u τ : M.H τ) := by
  refine (dense_pi Set.univ fun τ _ => Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M τ).mono fun x hx => ?_
  exact ⟨fun τ => ⟨x τ, hx τ trivial⟩, rfl⟩

theorem coe_update [DecidableEq D.what₂.Tau] (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ')) =
      Function.update (fun τ' => (u τ' : M.H τ')) τ (w : M.H τ) := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

set_option maxHeartbeats 1000000 in

theorem exists_of_isMultMap (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : IsMultMap θ M ∅ (fun _ => 1) T) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  classical
  have h𝓕 := isFundamentalDomain_stdDom (GQ V) μ
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := ∅) (χ := fun _ => 1) hP μ (stdDom (GQ V))
    hθ inferInstance h𝓕 T (Submodule.subset_span hT) T (Submodule.subset_span hT)
  have hm : ∀ u, MemL2Quotient (GQ V) μ (T u) := by
    intro u
    refine (memL2_iff_fundamental_domain h𝓕).2 ⟨(hT.aut u).left, ?_⟩
    refine (memLp_two_iff_integrable_sq_norm (hT.aut u).cont.measurable.aestronglyMeasurable).2
      ((hc u u).1.norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨F, hFl, hF⟩ : ∃ F : M.Vec → DividedPowerChartLift V μ, (∀ u, lift (GQ V) (F u) =ᵐ[μ] T u) ∧
      ∀ u u', ⟪F u, F u'⟫_ℂ = c * ∏ τ, ⟪(u τ : M.H τ), (u' τ : M.H τ)⟫_ℂ := by
    refine ⟨fun u => (hm u).toL2, fun u => (hm u).lift_toL2_ae_eq, fun u u' => ?_⟩
    rw [← (hc u u').2, MemL2Quotient.inner_toL2_eq_theta_pairing (hm u') (hm u), pet_eq h𝓕 (hT.aut u').left (hT.aut u).left]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [RCLike.star_def]
    ring
  obtain ⟨K, _, _, t0, ht0⟩ := GlobalTheory.HilbTensorExists.exists_pre M.H
  obtain ⟨L, _, _, _, s, hs, hd⟩ := GlobalTheory.HilbTensorExists.exists_complete_dense t0
  have hs' : ∀ x y, ⟪s x, s y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := fun x y => (hs x y).trans (ht0 x y)
  have hvec := denseRange_vec M
  have hdense := dense_span_tens s hs' hd _ hvec
  have hG : ∀ u u' : M.Vec, ⟪F u, F u'⟫_ℂ = c * ⟪s (fun τ => (u τ : M.H τ)), s (fun τ => (u' τ : M.H τ))⟫_ℂ := fun u u' => by
    rw [hF, hs']
  obtain ⟨A, hA⟩ := exists_extend (ι := M.Vec) (fun u => s fun τ => (u τ : M.H τ)) F hdense c hG
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), ∀ u : M.Vec, Φ (fun τ => (u τ : M.H τ)) = F u :=
    ⟨A.compContinuousMultilinearMap (tensML s hs' hd), hA⟩
  refine ⟨Φ, (mem_homDS hθ).2 ⟨fun y => ?_, fun τ g hg y => ?_⟩, fun u => ?_⟩
  · refine hvec.induction_on y ((Submodule.isClosed_topologicalClosure _).preimage Φ.cont) fun u => ?_
    show Φ _ ∈ GlobalTheory.Cusp.L2cusp V μ
    rw [hΦ u]
    exact GlobalTheory.Cusp.mem_L2cusp_of_ae_eq ⟨(hT.aut u).cont, (hT.aut u).left, hT.cusp u⟩ (hFl u)
  · have h1 : Continuous fun y : (∀ τ, M.H τ) => Φ (Function.update y τ (M.rep τ g (y τ))) :=
      Φ.cont.comp (continuous_id.update τ ((M.rep τ g).continuous.comp (continuous_apply τ)))
    have h2 : Continuous fun y : (∀ τ, M.H τ) => RG V μ (atTau θ V τ g) (Φ y) :=
      (RG V μ (atTau θ V τ g)).continuous.comp Φ.cont
    refine congrFun (hvec.equalizer h1 h2 (funext fun u => ?_)) y
    let w : M.sm τ := ⟨M.rep τ g (u τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg _ (u τ).2⟩
    have e1 := hT.equiv τ g hg u w rfl
    have e2 : Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ)) =
        fun τ' => ((Function.update u τ w τ' : M.sm τ') : M.H τ') := (coe_update u τ w).symm
    show Φ (Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ g (u τ))) =
      RG V μ (atTau θ V τ g) (Φ fun τ' => (u τ' : M.H τ'))
    rw [e2, hΦ (Function.update u τ w), hΦ u]
    refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
    refine (hFl _).trans ?_
    rw [e1]
    refine (EventuallyEq.trans ?_ (lift_R _ _).symm)
    exact ((measurePreserving_mul_right μ (atTau θ V τ g)).quasiMeasurePreserving.ae (hFl u)).mono
      fun x hx => hx.symm
  · rw [hΦ u]
    exact hFl u

theorem eq_of_represents {μ : Measure (GA D V)} [μ.IsHaarMeasure] {T : MMap M}
    {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)}
    (h : ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v)
    (h' : ∀ v : M.Vec, lift (GQ V) (Φ' fun τ => (v τ : M.H τ)) =ᵐ[μ] T v) : Φ = Φ' := by
  refine ContinuousMultilinearMap.ext fun y => congrFun ((denseRange_vec M).equalizer Φ.cont Φ'.cont
    (funext fun v => ?_)) y
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((h v).trans (h' v).symm)

theorem exists_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {T : MMap M}
    (hT : T ∈ GlobalTheory.CuspMult.allMaps θ M) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧
      ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact exists_of_isMultMap hP hθ μ hT
  | zero =>
    refine ⟨0, zero_mem _, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
    exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)
  | add T T' _ _ ih ih' =>
    obtain ⟨Φ, h1, h2⟩ := ih
    obtain ⟨Φ', h1', h2'⟩ := ih'
    refine ⟨Φ + Φ', add_mem h1 h1', fun v => ?_⟩
    simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add _ _)) ((h2 v).add (h2' v))
  | smul a T _ ih =>
    obtain ⟨Φ, h1, h2⟩ := ih
    refine ⟨a • Φ, Submodule.smul_mem _ a h1, fun v => ?_⟩
    simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
    exact Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul a _)) ((h2 v).const_smul a)

theorem existsUnique_intertwiner : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∃! Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ), Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro hP D θ hθ V S M μ _ _ T hT
  obtain ⟨Φ, h1, h2⟩ := exists_of_mem hP hθ μ hT
  exact ⟨Φ, ⟨h1, h2⟩, fun Φ' h' => eq_of_represents h'.2 h2⟩

end GlobalTheory.CuspIntertwiner

end
