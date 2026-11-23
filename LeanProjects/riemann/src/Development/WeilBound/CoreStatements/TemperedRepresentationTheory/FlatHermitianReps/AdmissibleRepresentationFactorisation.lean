import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)
open scoped Topology

theorem finiteDimensional_of_compact_bdd {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsCompactOperator T) (X : Submodule ℂ E) {c : ℝ} (hc : 0 < c)
    (hX : ∀ x ∈ X, c * ‖x‖ ≤ ‖T x‖) : FiniteDimensional ℂ X := by
  set Y := X.topologicalClosure with hYdef
  have hcl : IsClosed {x : E | c * ‖x‖ ≤ ‖T x‖} :=
    isClosed_le (continuous_const.mul continuous_norm) (continuous_norm.comp T.continuous)
  have hY : ∀ y ∈ Y, c * ‖y‖ ≤ ‖T y‖ := by
    intro y hy
    have hy' : y ∈ closure (X : Set E) := by rwa [← Submodule.topologicalClosure_coe]
    exact closure_minimal (fun x hx => hX x hx) hcl hy'
  haveI : CompleteSpace Y := X.isClosed_topologicalClosure.completeSpace_coe
  let f : Y →L[ℂ] E := T ∘L Y.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) f := by
    refine f.antilipschitz_of_bound fun y => ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hc.le)]
    exact (le_inv_mul_iff₀ hc).2 (hY y y.2)
  have hemb : Topology.IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  have hK := hT.isCompact_closure_image_closedBall 1
  have hpre : IsCompact (f ⁻¹' closure (T '' Metric.closedBall 0 1)) := hemb.isCompact_preimage hK
  have hball : IsCompact (Metric.closedBall (0 : Y) 1) :=
    hpre.of_isClosed_subset Metric.isClosed_closedBall fun y hy =>
      subset_closure ⟨(y : E), mem_closedBall_zero_iff.2 (mem_closedBall_zero_iff.1 hy), rfl⟩
  haveI : FiniteDimensional ℂ Y := FiniteDimensional.of_isCompact_closedBall₀ (𝕜 := ℂ) zero_lt_one hball
  exact Submodule.finiteDimensional_of_le X.le_topologicalClosure

theorem mem_fixed_imp {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K : Subgroup G} {x : X} (h : x ∈ fixed ρ K) : ∀ g ∈ K, ρ g x = x := fun g hg => by
  simpa using h ⟨g, hg⟩

noncomputable def phiDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) : ℂ :=
  ∏ τ, ⟪unitVec (M.H τ), dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (unitVec (M.H τ))⟫_ℂ

theorem continuous_phiDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Continuous (phiDS M) := by
  unfold phiDS
  refine continuous_finsetProd _ fun τ _ => continuous_const.inner ?_
  exact ((isIrrUnitary_dsRep M τ).unitary.continuous_apply (unitVec (M.H τ))).comp
    (continuous_projArch D.sp.cm.sig V.gram (placeOf D τ))

theorem phiDS_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : phiDS M 1 = 1 := by
  unfold phiDS
  refine Finset.prod_eq_one fun τ _ => ?_
  have : Nontrivial (M.H τ) := (isIrrUnitary_dsRep M τ).irred.1
  simp only [map_one, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, norm_unitVec]
  simp

set_option maxHeartbeats 400000 in
theorem inner_apply_homDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}
    (hπ : IsUnitaryRep π) {K : Subgroup (GfC V)} {Φ : ContinuousMultilinearMap ℂ M.H H} (hΦ : Φ ∈ homDS M π ⊤)
    (hfix : ∀ k ∈ K, ∀ y, π (k : GA D V) (Φ y) = Φ y) (g : GA D V) (hg : toFin V g ∈ K) :
    ⟪Φ (fun τ => unitVec (M.H τ)), π g (Φ (fun τ => unitVec (M.H τ)))⟫_ℂ =
      ⟪Φ (fun τ => unitVec (M.H τ)), Φ (fun τ => unitVec (M.H τ))⟫_ℂ * phiDS M g := by
  classical
  have e1 : π g (Φ (fun τ => unitVec (M.H τ))) =
      π (toInf V g : GA D V) (π (toFin V g : GA D V) (Φ (fun τ => unitVec (M.H τ)))) := by
    conv_lhs => rw [← toInf_mul_toFin g]
    rw [map_mul]; rfl
  rw [e1, hfix _ hg, GlobalTheory.TrAct.toInf_apply_homDS D V S M H π ⊤ Φ hΦ g]
  rw [inner_eq_bePi (fun τ => isIrrUnitary_dsRep M τ) hπ hΦ hΦ]
  rfl

set_option maxHeartbeats 400000 in
theorem eq_zero_of_apply_unitVec {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}
    (hπ : IsUnitaryRep π) {Φ : ContinuousMultilinearMap ℂ M.H H} (hΦ : Φ ∈ homDS M π ⊤)
    (h0 : Φ (fun τ => unitVec (M.H τ)) = 0) : Φ = 0 := by
  classical
  by_contra hne
  have hpos := bePi_self_pos (fun τ => isIrrUnitary_dsRep M τ) hπ hΦ hne
  simp only [bePi] at hpos
  rw [h0, inner_zero_left] at hpos
  simp at hpos

set_option maxHeartbeats 400000 in

theorem finiteDimensional_of_bump {G E : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {π : G →* (E →L[ℂ] E)} (hπ : IsUnitaryRep π) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {φ : G → ℂ} (hφc : Continuous φ) (hφ1 : φ 1 = 1) {A : Set G} (hA : IsOpen A) (h1 : (1 : G) ∈ A)
    (hbump : ∀ N ∈ 𝓝 (1 : G), ∃ b : G → ℝ, Continuous b ∧ HasCompactSupport b ∧ 0 ≤ b ∧ b 1 = 1 ∧
      Function.support b ⊆ N ∧ IsCompactOperator (repOp π μ fun g => (b g : ℂ)))
    (X : Submodule ℂ E) (hX : ∀ x ∈ X, ∀ g ∈ A, ⟪x, π g x⟫_ℂ = ⟪x, x⟫_ℂ * φ g) : FiniteDimensional ℂ X := by
  set N : Set G := A ∩ {g | 1 / 2 < (φ g).re} with hNdef
  have hN : N ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds (hA.inter (isOpen_lt continuous_const (Complex.continuous_re.comp hφc))) ⟨h1, ?_⟩
    show 1 / 2 < (φ 1).re
    rw [hφ1]; norm_num
  obtain ⟨b, hbc, hbcs, hb0, hb1, hbs, hcpt⟩ := hbump N hN
  set f : G → ℂ := fun g => (b g : ℂ) with hfdef
  have hfc : Continuous f := Complex.continuous_ofReal.comp hbc
  have hfcs : HasCompactSupport f := hbcs.comp_left Complex.ofReal_zero
  set J : ℂ := ∫ g, f g * φ g ∂μ with hJdef
  have hint : Integrable (fun g => f g * φ g) μ :=
    (hfc.mul hφc).integrable_of_hasCompactSupport (hfcs.mono (Function.support_mul_subset_left _ _))
  have hsupp : ∀ g, b g ≠ 0 → g ∈ N := fun g hg => hbs (Function.mem_support.2 hg)
  have hJre : J.re = ∫ g, b g * (φ g).re ∂μ := by
    rw [hJdef, ← RCLike.re_to_complex, ← integral_re hint]
    congr 1
    funext g
    simp [hfdef]
  have hJpos : 0 < J.re := by
    rw [hJre]
    refine (hbc.mul (Complex.continuous_re.comp hφc)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := 1) ?_ ?_ ?_
    · exact hbcs.mono (Function.support_mul_subset_left _ _)
    · intro g
      by_cases hg : b g = 0
      · simp [hg]
      · exact mul_nonneg (hb0 g) ((hsupp g hg).2.le.trans' (by norm_num))
    · simp [hb1, hφ1]
  have hJ0 : J ≠ 0 := fun h => by rw [h] at hJpos; simp at hJpos
  have hbound : ∀ x ∈ X, ‖J‖ * ‖x‖ ≤ ‖repOp π μ f x‖ := by
    intro x hxX
    have hx : ⟪x, repOp π μ f x⟫_ℂ = ⟪x, x⟫_ℂ * J := by
      rw [hπ.inner_repOp hfc hfcs, hJdef, ← integral_const_mul]
      congr 1
      funext g
      by_cases hg : b g = 0
      · simp [hfdef, hg]
      · rw [hX x hxX g (hsupp g hg).1]; ring
    have hn : ‖⟪x, x⟫_ℂ * J‖ = ‖x‖ ^ 2 * ‖J‖ := by
      rw [norm_mul, inner_self_eq_norm_sq_to_K]; simp
    have hcs : ‖x‖ ^ 2 * ‖J‖ ≤ ‖x‖ * ‖repOp π μ f x‖ := by
      rw [← hn, ← hx]; exact norm_inner_le_norm _ _
    rcases (norm_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · refine le_of_mul_le_mul_left ?_ hpos
      have : ‖x‖ * (‖J‖ * ‖x‖) = ‖x‖ ^ 2 * ‖J‖ := by ring
      linarith
  exact finiteDimensional_of_compact_bdd _ hcpt X (norm_pos_iff.2 hJ0) hbound

set_option maxHeartbeats 400000 in
theorem admissible_representation_factorisation : AdmSt := by
  intro D V S M μ _ H _ _ _ π hπ hcpt hU
  classical
  refine ⟨isSmooth_smoothRep _, fun K hKo hKc => ?_⟩
  let ev : fixed (finPartDSSm M hU) K →ₗ[ℂ] H :=
    (ContinuousMultilinearMap.apply ℂ M.H H (fun τ => unitVec (M.H τ))).toLinearMap ∘ₗ
      (homDS M π ⊤).subtype ∘ₗ (smoothPart (finPartDS M hU)).subtype ∘ₗ (fixed (finPartDSSm M hU) K).subtype
  have hev : ∀ Φ : fixed (finPartDSSm M hU) K,
      ev Φ = (((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H)
        (fun τ => unitVec (M.H τ)) := fun Φ => rfl
  have hfix : ∀ Φ : fixed (finPartDSSm M hU) K, ∀ k ∈ K, ∀ y,
      π (k : GA D V) ((((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y) =
        (((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y :=
    fun Φ k hk y => congrArg (fun Ψ : smoothPart (finPartDS M hU) =>
      ((Ψ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y) (mem_fixed_imp Φ.2 k hk)
  have hX : ∀ x ∈ LinearMap.range ev, ∀ g ∈ {g : GA D V | toFin V g ∈ K},
      ⟪x, π g x⟫_ℂ = ⟪x, x⟫_ℂ * phiDS M g := by
    rintro _ ⟨Φ, rfl⟩ g hg
    rw [hev Φ]
    exact inner_apply_homDS hπ ((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤).2 (hfix Φ) g hg
  have hbump : ∀ N ∈ 𝓝 (1 : GA D V), ∃ b : GA D V → ℝ, Continuous b ∧ HasCompactSupport b ∧ 0 ≤ b ∧ b 1 = 1 ∧
      Function.support b ⊆ N ∧ IsCompactOperator (repOp π μ fun g => (b g : ℂ)) := by
    intro N hN
    obtain ⟨b, hb, hb0, hb1, hbs⟩ := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
    have hfc := continuous_of_mem_ccAd hb
    exact ⟨b, Complex.continuous_re.comp hfc.1, hfc.2.comp_left (g := Complex.re) Complex.zero_re, hb0, hb1, hbs,
      hcpt _ hb⟩
  have h1 : (1 : GA D V) ∈ {g : GA D V | toFin V g ∈ K} := by
    show toFin V 1 ∈ K
    rw [map_one]; exact K.one_mem
  have : FiniteDimensional ℂ (LinearMap.range ev) :=
    finiteDimensional_of_bump hπ μ (continuous_phiDS M) (phiDS_one M) (hKo.preimage (continuous_toFin V)) h1
      hbump _ hX
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Φ hΦ
    rw [hev Φ] at hΦ
    have h0 := eq_zero_of_apply_unitVec hπ ((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤).2 hΦ
    exact Subtype.ext (Subtype.ext (Subtype.ext h0))
  exact Module.Finite.of_injective ev.rangeRestrict fun a b e => hinj (congrArg Subtype.val e)

end MainStatements.Flath2
