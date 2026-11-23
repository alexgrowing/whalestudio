import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct

noncomputable section

namespace GlobalTheory.Mem.DerClosed

section Abstract

open GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind NormedSpace Filter Asymptotics
open scoped ContDiff Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hasFDerivAt_diag {f f' : P → ℝ → ℂ} {A : P →L[ℝ] ℂ} (l : P →L[ℝ] ℝ) (h1 : HasFDerivAt (fun p => f p 0) A 0)
    (h2 : ∀ p t, HasDerivAt (f p) (f' p t) t) (h3 : ContinuousAt (fun q : P × ℝ => f' q.1 q.2) (0, 0)) :
    HasFDerivAt (fun p => f p (l p)) (A + l.smulRight (f' 0 0)) 0 := by
  have key : HasFDerivAt (fun p => f p (l p) - f p 0) (l.smulRight (f' 0 0)) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine IsLittleO.trans_isBigO (g := fun p => l p) ?_ (l.isBigO_id _)
    rw [isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, h4⟩ := Metric.continuousAt_iff.1 h3 ε hε
    have e1 : ∀ᶠ p in 𝓝 (0 : P), ‖p‖ < δ := (continuous_norm.tendsto' 0 0 norm_zero).eventually (gt_mem_nhds hδ)
    have e2 : ∀ᶠ p in 𝓝 (0 : P), ‖l p‖ < δ :=
      (l.continuous.norm.tendsto' 0 0 (by simp)).eventually (gt_mem_nhds hδ)
    filter_upwards [e1, e2] with p q1 q2
    have := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => f p t - t • f' 0 0) (f' := fun t => f' p t - f' 0 0) (C := ε) (x := 0) (y := l p)
      (fun t _ => ((h2 p t).sub (by simpa using (hasDerivAt_id t).smul_const (f' 0 0))).hasDerivWithinAt)
      (fun t ht => by
        have := @h4 (p, t) (by
          rw [Prod.dist_eq, max_lt_iff]
          exact ⟨by simpa using q1, ht⟩)
        rw [dist_eq_norm] at this
        exact this.le)
      (Metric.mem_ball_self hδ) (by simpa using q2)
    simp only [zero_add, map_zero, sub_self, sub_zero, zero_smul, ContinuousLinearMap.smulRight_apply] at this ⊢
    rwa [sub_right_comm]
  have := h1.fun_add key
  simpa using this

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

omit [FiniteDimensional ℝ 𝔸] in
theorem unit_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) : σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem expMap_add (H : IsLieData σ j s) (X : L) (t u : ℝ) :
    expMap j s ((t + u) • X) = expMap j s (t • X) * expMap j s (u • X) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold expMap
  rw [← H.mul _ _ (exp_unitary H _) (exp_unitary H _), add_smul, map_add, NormedSpace.exp_add_of_commute]
  rw [map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

theorem exists_coord (H : IsLieData σ j s) (J : L →L[ℝ] 𝔸) (hJ : ∀ X, J X = j X) {ι : Type} (l : ι → P →L[ℝ] ℝ)
    (b : ι → L) {φ : G → ℂ} {φ' : ι → G → ℂ}
    (hd : ∀ i g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • b i))) (φ' i g) 0) (g : G)
    (hc : ∀ i, ContinuousOn (fun u => φ' i (g * s u)) {u | σ u * u = 1}) (S : Finset ι) :
    ∃ c : P → 𝔸, ContDiff ℝ ∞ c ∧ (∀ p, σ (c p) * c p = 1) ∧ c 0 = 1 ∧
      HasFDerivAt c (J ∘L ∑ i ∈ S, (l i).smulRight (b i)) 0 ∧
      HasFDerivAt (fun p => φ (g * s (c p))) (∑ i ∈ S, (l i).smulRight (φ' i g)) 0 := by
  classical
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 1, contDiff_const, fun _ => by simp [H.one], rfl, ?_, ?_⟩
    · simpa using hasFDerivAt_const (1 : 𝔸) (0 : P)
    · simpa using hasFDerivAt_const (φ (g * s 1)) (0 : P)
  | insert i S hi ih =>
    obtain ⟨c, h1, h2, h4, h5, h6⟩ := ih
    let A : P →L[ℝ] L := (l i).smulRight (b i)
    have hA : ContDiff ℝ ∞ fun p => exp (J (A p)) := contDiff_exp.comp (J ∘L A).contDiff
    have hu : ∀ X, σ (exp (J X)) * exp (J X) = 1 := fun p => by rw [hJ]; exact exp_unitary H _
    refine ⟨fun p => c p * exp (J (A p)), h1.mul hA, fun p => unit_mul H (h2 p) (hu _), by simp [h4], ?_, ?_⟩
    · have hd : HasFDerivAt (fun p => exp (J (A p))) (J ∘L A) 0 := by
        have := HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : P)
          (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) (J ∘L A).hasFDerivAt
        exact this
      refine (h5.mul' hd).congr_fderiv ?_
      rw [Finset.sum_insert hi]
      ext p
      simp [h4, A]
    · have e : ∀ p (t : ℝ), s (c p * exp (J (t • b i))) = s (c p) * expMap j s (t • b i) := fun p t => by
        rw [H.mul _ _ (h2 p) (hu _), hJ, expMap]
      have := hasFDerivAt_diag (f := fun p t => φ (g * s (c p * exp (J (t • b i)))))
        (f' := fun p t => φ' i (g * s (c p * exp (J (t • b i))))) (l i) (by simpa using h6) (fun p t => ?_) ?_
      · rw [Finset.sum_insert hi, add_comm]
        simpa [h4, map_one_eq H, A] using this
      · have k := hd i (g * s (c p * exp (J (t • b i))))
        have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
        refine k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
        beta_reduce
        rw [e, e, mul_assoc, mul_assoc, ← expMap_add H, add_sub_cancel]
      · refine ((hc i).comp_continuous (f := fun q : P × ℝ => c q.1 * exp (J (q.2 • b i))) ?_
          fun q => unit_mul H (h2 _) (hu _)).continuousAt
        exact (h1.continuous.comp continuous_fst).mul (contDiff_exp.continuous.comp (by fun_prop))

theorem hasFDerivAt_expMap (H : IsLieData σ j s) (hl : HasLog σ j) {ι : Type} [Fintype ι] (l : ι → L →L[ℝ] ℝ)
    (b : ι → L) (hb : ∑ i, (l i).smulRight (b i) = ContinuousLinearMap.id ℝ L) {φ : G → ℂ} {φ' : ι → G → ℂ}
    (hd : ∀ i g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • b i))) (φ' i g) 0) (g : G)
    (hc : ∀ i, ContinuousOn (fun u => φ' i (g * s u)) {u | σ u * u = 1}) :
    HasFDerivAt (fun X => φ (g * expMap j s X)) (∑ i, (l i).smulRight (φ' i g)) 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  have : CompleteSpace L := FiniteDimensional.complete ℝ L
  let J : L →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap j
  obtain ⟨c, h1, h2, h4, h5, h6⟩ := exists_coord H J (fun _ => rfl) l b hd g hc Finset.univ
  rw [hb, ContinuousLinearMap.comp_id] at h5
  obtain ⟨Λ, l1, l2, l3⟩ := hl
  have hΛ : Λ 1 = 0 := by simpa using l3.self_of_nhds
  have l4 := (l1.differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun X : L => exp (j X)) J 0 :=
    HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : L)
        (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) J.hasFDerivAt
  have l5 : fderiv ℝ Λ 1 ∘L J = ContinuousLinearMap.id ℝ L := by
    have := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) (0 : L) (by simpa using l4) hd
    exact this.unique ((hasFDerivAt_id (0 : L)).congr_of_eventuallyEq l3)
  have hΦ : ContDiffAt ℝ ∞ (Λ ∘ c) 0 := ContDiffAt.comp 0 (by rwa [h4]) h1.contDiffAt
  have hΦ' : HasFDerivAt (Λ ∘ c) (ContinuousLinearEquiv.refl ℝ L : L →L[ℝ] L) 0 := by
    have := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) _ (by rwa [h4]) h5
    rwa [l5] at this
  have h0 : (Λ ∘ c) 0 = 0 := by simp [h4, hΛ]
  have hs := hΦ.hasStrictFDerivAt' hΦ' (by simp)
  have p1 := hs.to_localInverse.hasFDerivAt
  have p2 := hs.localInverse_apply_image
  have p3 := hs.eventually_right_inverse
  rw [h0] at p1 p2 p3
  set Ψ := hs.localInverse _ _ _
  have ht : Tendsto (fun X => c (Ψ X)) (𝓝 0) (𝓝 1) := by
    have := (h1.continuous.tendsto (Ψ 0)).comp p1.continuousAt
    rwa [p2, h4] at this
  refine (HasFDerivAt.comp (g := fun p => φ (g * s (c p))) (0 : L) (by rw [p2]; exact h6) p1).congr_of_eventuallyEq ?_
  filter_upwards [p3, ht.eventually l2] with X q1 q2
  have := q2 (h2 _)
  simp only [Function.comp] at q1 ⊢
  rw [q1] at this
  rw [← this, expMap]

theorem sm_of_closed (H : IsLieData σ j s) (hl : HasLog σ j) (T : Set L) (hT : Submodule.span ℝ T = ⊤)
    (𝒮 : Set (G → ℂ)) (hc : ∀ φ ∈ 𝒮, ∀ g, ContinuousOn (fun u => φ (g * s u)) {u | σ u * u = 1})
    (hd : ∀ φ ∈ 𝒮, ∀ X ∈ T, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • X))) (φ' g) 0) :
    ∀ φ ∈ 𝒮, Sm (expMap j s) φ := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  let J : L →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap j
  let b₀ := Module.Basis.ofSpan hT.ge
  have := FiniteDimensional.fintypeBasisIndex b₀
  let b := b₀.reindex (Fintype.equivFin _)
  have hb : ∀ i, b i ∈ T := fun i => Module.Basis.ofSpan_subset hT.ge ⟨_, (b₀.reindex_apply _ i).symm⟩
  let l := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hl' : ∑ i, (l i).smulRight (b i) = ContinuousLinearMap.id ℝ L := ContinuousLinearMap.ext fun X => by
    rw [_root_.sum_apply]
    exact b.sum_repr X
  obtain ⟨c, hcd⟩ : ∃ c : L → 𝔸, c = fun X => exp (j X) := ⟨_, rfl⟩
  have hE : ContDiff ℝ ∞ c := hcd ▸ contDiff_exp.comp J.contDiff
  have hu : ∀ p, σ (c p) * c p = 1 := hcd ▸ exp_unitary H
  have hσ : ContDiff ℝ ∞ fun p => σ (c p) := (LinearMap.toContinuousLinearMap σ).contDiff.comp hE
  obtain ⟨Λ, h1, h2, h3⟩ := id hl
  have hΛ : Λ 1 = 0 := by simpa using h3.self_of_nhds
  have key : ∀ n : ℕ, ∀ φ ∈ 𝒮, ∀ g, ContDiff ℝ n fun p => φ (g * s (c p)) := by
    intro n
    induction n with
    | zero => exact fun φ hφ g => contDiff_zero.2 ((hc φ hφ g).comp_continuous hE.continuous hu)
    | succ n ih =>
      intro φ hφ g
      choose φ' m1 m2 using fun i => hd φ hφ _ (hb i)
      have der : ∀ p₀, HasFDerivAt (fun p => φ (g * s (c p))) ((∑ i, (l i).smulRight (φ' i (g * s (c p₀)))) ∘L
          (fderiv ℝ Λ 1 ∘L (σ (c p₀) • fderiv ℝ c p₀))) p₀ := fun p₀ => by
        have hr : c p₀ * σ (c p₀) = 1 := by
          haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
          exact mul_eq_one_comm.1 (hu p₀)
        have hd : HasFDerivAt (fun p => σ (c p₀) * c p) (σ (c p₀) • fderiv ℝ c p₀) p₀ :=
          (hE.differentiable (by simp) p₀).hasFDerivAt.const_mul _
        have ht : Tendsto (fun p => σ (c p₀) * c p) (𝓝 p₀) (𝓝 1) := by
          have := hd.continuousAt.tendsto
          rwa [hu p₀] at this
        have hu' : ∀ p, σ (σ (c p₀) * c p) * (σ (c p₀) * c p) = 1 := fun p =>
          unit_mul H (by rw [H.invol, hr]) (hu p)
        have h4 := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) p₀
          (by rw [hu p₀]; exact (h1.differentiableAt (by simp)).hasFDerivAt) hd
        have h5 := HasFDerivAt.comp (g := fun X : L => φ (g * s (c p₀) * expMap j s X)) p₀
          (by
            rw [Function.comp, hu p₀, hΛ]
            exact hasFDerivAt_expMap H hl l b hl' m2 _ fun i => hc _ (m1 i) _) h4
        refine h5.congr_of_eventuallyEq ((ht.eventually h2).mono fun p hp => ?_)
        simp only [Function.comp, expMap]
        rw [hp (hu' p), mul_assoc, ← H.mul _ _ (hu p₀) (hu' p), ← mul_assoc, hr, one_mul]
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun p => (der p).differentiableAt, by simp, fun y => ?_⟩
      simp only [(der _).fderiv, ContinuousLinearMap.comp_apply, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smul_apply]
      refine ContDiff.sum fun i _ => ContDiff.smul (𝕜' := ℝ) ?_ (ih _ (m1 i) g)
      have k : ContDiff ℝ ∞ fun p => fderiv ℝ c p y :=
        (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact contDiff_infty.1 ((l i ∘L fderiv ℝ Λ 1).contDiff.comp (hσ.mul k)) n
  intro φ hφ g
  subst hcd
  exact contDiff_infty.2 fun n => key n φ hφ g

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SmoothForms

theorem continuousOn_secInf {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) :
    ContinuousOn (secInf θ V) {u | sigInf V u * u = 1} := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have h := GlobalTheory.RealLift.continuousOn_prodAt hθ V Finset.univ.toList
  refine ContinuousOn.congr (h.mono fun u hu => (unit_iff R u).1 hu) fun u hu => ?_
  refine R.2.2.1 _ (secInf_spec R hu).1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ u) fun τ => ?_
  rw [(secInf_spec R hu).2, GlobalTheory.RealLift.infMat_prodAt hθ V ((unit_iff R u).1 hu) τ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]

theorem mem_smFun_of_closed : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ 𝒮 : Set (GA D V → ℂ), (∀ φ ∈ 𝒮, Continuous φ) → (∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt V τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) → ∀ φ ∈ 𝒮, φ ∈ SmFun θ V := by
  intro D θ hθ V 𝒮 hc hd φ hφ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hT : Submodule.span ℝ {Y : LieN V | ∃ τ X, Y = atPlace V τ X} = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have : X = ∑ τ, (atPlace V τ (X τ) : LieN V) := (sum_atPlace X).symm
    rw [this]
    exact sum_mem fun τ _ => Submodule.subset_span ⟨τ, _, rfl⟩
  refine (smooth_iff R φ).2 (sm_of_closed (isLieData R) (hasLog R) _ hT 𝒮 (fun ψ hψ g => ?_) ?_ φ hφ)
  · exact (hc ψ hψ).comp_continuousOn (continuousOn_const.mul (continuousOn_secInf hθ V))
  · rintro ψ hψ _ ⟨τ, X, rfl⟩
    obtain ⟨ψ', h1, h2⟩ := hd ψ hψ τ X.1 X.2
    refine ⟨ψ', h1, fun g => ?_⟩
    have := h2 g
    simp only [oneP_eq R] at this
    exact this

end GlobalTheory.Mem.DerClosed

end
