import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionTensorPullbackRingHomBijective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConstAddEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicGroupLawGermStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SaturatedLatticeQuotientCountStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.QuotLoc

open Matrix Metric Filter Topology GroundTheory.Heights₂.Heights.Regular

variable {n a : ℕ}

lemma expCover_mem_punctured (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} := by
  refine ⟨expCover_mem_ball h hw, fun i hi => ?_⟩
  simp only [expCover, hi, if_true]
  exact Complex.exp_ne_zero _

lemma exists_mem_logCover (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0}) :
    ∃ w ∈ logCover h, expCover a w = z := by
  have hlt : ∀ k : Fin n, ‖z k‖ < 1 := fun k =>
    (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)
  refine ⟨logLift a z, ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    have h0 := hz.2 _ hi
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.2 h0) (hlt _)
  · simp only [logLift, if_neg (not_lt.2 hk)]
    exact hlt k
  · funext k
    by_cases hk : k.val < a
    · simp only [expCover, logLift, if_pos hk]
      exact Complex.exp_log (hz.2 k hk)
    · simp only [expCover, logLift, if_neg hk]

lemma differentiable_expCover : Differentiable ℂ (expCover (n := n) a) := by
  refine differentiable_pi.2 fun k => ?_
  by_cases hk : k.val < a
  · simp only [expCover, if_pos hk]
    exact Complex.differentiable_exp.comp (differentiable_apply k)
  · simp only [expCover, if_neg hk]
    exact differentiable_apply k

lemma expCover_add_single (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hki : k = Fin.castLE h i
  · subst hki
    simp [expCover, i.isLt, Complex.exp_add]
  · simp [expCover, Pi.single_eq_of_ne hki]

lemma add_single_mem_logCover (h : a ≤ n) (i : Fin a) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine (LogCoverDescent.add_mem_logCover_iff h (fun k => ?_) (fun k hk => ?_) w).2 hw
  · by_cases hki : k = Fin.castLE h i
    · subst hki; simp
    · simp [Pi.single_eq_of_ne hki]
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      exact absurd i.2 (not_lt.2 hk)
    simp [Pi.single_eq_of_ne hki]

lemma eq_at_zero_of_eqOn {F : Type*} [TopologicalSpace F] [T2Space F]
    {f f' : (Fin n → ℂ) → F} (hf : ContinuousAt f 0) (hf' : ContinuousAt f' 0)
    (he : ∀ z ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0}, f z = f' z) :
    f 0 = f' 0 := by
  let u : ℕ → Fin n → ℂ := fun k _ => ((1 / ((k : ℝ) + 2) : ℝ) : ℂ)
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 2) := fun k => by positivity
  have hlt : ∀ k : ℕ, 1 / ((k : ℝ) + 2) < 1 := fun k => by
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun j => ?_
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k => ?_
      simp only [Function.comp]
      push_cast
      ring_nf
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [u, Function.comp_def] using h2
  have hmem : ∀ k, u k ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} := by
    intro k
    refine ⟨?_, fun i _ => ?_⟩
    · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro j
      simp only [u, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos k)]
      exact hlt k
    · simp only [u]
      exact_mod_cast (hpos k).ne'
  have t1 := hf.tendsto.comp hu
  have t2 := hf'.tendsto.comp hu
  refine tendsto_nhds_unique t1 (t2.congr fun k => ?_)
  exact (he _ (hmem k)).symm

lemma coiso_of_count {Λ M : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [AddCommGroup M] (E : LinearMap.BilinForm ℤ Λ) (hbij : Function.Bijective E)
    (halt : ∀ x, E x x = 0) (l : M →ₗ[ℤ] Λ) (hinj : Function.Injective l)
    (hsat : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ LinearMap.range l → x ∈ LinearMap.range l)
    (hcount : ∀ N : ℕ, 0 < N → ∃ T : Set (M ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))),
      Nat.card (M ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * Nat.card T =
        N ^ Module.finrank ℤ Λ ∧
      ∀ x y : M, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ E (l x) (l y)) :
    ∀ x, (∀ y ∈ LinearMap.range l, E x y = 0) → x ∈ LinearMap.range l := by
  refine GlobalTheory.T.saturated_lattice_quotient_count Λ E hbij halt (LinearMap.range l) hsat fun N hN => ?_
  obtain ⟨T, hcard, hdvd⟩ := hcount N hN
  let e : M ≃ₗ[ℤ] LinearMap.range l := LinearEquiv.ofInjective l hinj
  have hmap : (LinearMap.range ((N : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).map (e : M →ₗ[ℤ] _) =
      LinearMap.range ((N : ℤ) • (LinearMap.id : LinearMap.range l →ₗ[ℤ] LinearMap.range l)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨y', rfl⟩
      refine ⟨(N : ℤ) • e.symm y', ⟨e.symm y', by simp⟩, by simp⟩
  let Q := Submodule.Quotient.equiv _ _ e hmap
  refine ⟨Q '' T, ?_, ?_⟩
  · rw [Nat.card_image_of_injective Q.injective, ← Nat.card_congr Q.toEquiv]
    exact hcard
  · intro x y hx
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    have hx' : Submodule.Quotient.mk x' ∈ T := by
      obtain ⟨t, ht, hte⟩ := hx
      have : t = Submodule.Quotient.mk x' := Q.injective (by rw [hte]; rfl)
      exact this ▸ ht
    exact hdvd x' y' hx'

end GlobalTheory.CompanionTheory.Ar.Flat.QuotLoc

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix Metric Filter Topology GroundTheory.Heights₂.Heights.Regular QuotLoc

theorem exists_logPeriods_range_eq : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (Metric.ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (L.P w).range = Γ (GroundTheory.Heights₂.Heights.Regular.expCover a w) := by
  intro n a g h Λ _ _ _ E Γ Hf U Γ₀ S hU hrank halt hbij hpos hloc hS hadd hlim hspan hcount
  subst hU
  haveI : Countable Λ := (Module.finBasis ℤ Λ).equivFun.injective.countable
  have hmem : ∀ w ∈ logCover h, expCover a w ∈ _ := fun w hw => expCover_mem_punctured h hw
  have hBo := isOpen_logCover h
  have hBc := convex_logCover h
  have hBp : IsPreconnected (logCover h) := hBc.isPreconnected
  have hBn := logCover_nonempty h
  have hdiff : DifferentiableOn ℂ (expCover (n := n) a) (logCover h) :=
    differentiable_expCover.differentiableOn

  obtain ⟨P, hPhol, hP0⟩ := GlobalTheory.T.holomorphic_lattice_family_local n g Λ (logCover h) hBo hBc
    (fun w => Γ (expCover a w)) (fun w u v => (u ⬝ᵥ Hf (expCover a w) *ᵥ star v).im)
    (fun x y => (E x y : ℝ)) (by
      intro w₀ hw₀
      obtain ⟨N, hNo, hz, hNU, P, hPh, hPp⟩ := hloc _ (hmem w₀ hw₀)
      refine ⟨logCover h ∩ expCover a ⁻¹' N,
        hBo.inter (hNo.preimage (continuous_expCover a)), ⟨hw₀, hz⟩, Set.inter_subset_left,
        fun w => P (expCover a w), fun x => ?_, fun w hw => hPp _ hw.2⟩
      exact (hPh x).comp (hdiff.mono Set.inter_subset_left) (fun w hw => hw.2))
  have hP : ∀ w ∈ logCover h, Function.Injective (P w) ∧ (P w).range = Γ (expCover a w) ∧
      ∀ x y, (P w x ⬝ᵥ Hf (expCover a w) *ᵥ star (P w y)).im = (E x y : ℝ) := hP0

  have hT : ∀ i : Fin a, ∃ T : Λ ≃+ Λ, ∀ w ∈ logCover h, ∀ x,
      P (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) x = P w (T x) := by
    intro i
    refine exists_const_addEquiv_of_range_eq n g Λ Λ (logCover h) hBo hBp hBn P
      (fun w => P (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I))) hPhol
      (fun x => ?_) (fun w hw => ?_)
    · refine (hPhol x).comp (differentiableOn_id.add_const _) (fun w hw => ?_)
      exact add_single_mem_logCover h i hw
    · have hw' := add_single_mem_logCover h i hw
      refine ⟨(hP w hw).1, (hP _ hw').1, ?_⟩
      rw [(hP w hw).2.1, (hP _ hw').2.1, expCover_add_single]
  choose T hT using hT

  have hsec : ∀ x : Γ₀, ∃ l : Λ, ∀ w ∈ logCover h, S x (expCover a w) = P w l := by
    intro x
    refine exists_const_of_section_mem_range n g Λ (logCover h) hBo hBp hBn P
      (fun w => S x (expCover a w)) hPhol ?_ (fun w hw => ?_)
    · exact (hS x).1.comp hdiff (fun w hw => expCover_mem_ball h hw)
    · rw [(hP w hw).2.1]
      exact (hS x).2.2 _ (hmem w hw)
  choose l hl using hsec
  obtain ⟨w₀, hw₀⟩ := hBn
  have ladd : ∀ x y, l (x + y) = l x + l y := by
    intro x y
    apply (hP w₀ hw₀).1
    rw [← hl _ w₀ hw₀, map_add, ← hl _ w₀ hw₀, ← hl _ w₀ hw₀, hadd]
  let lam : Γ₀ →ₗ[ℤ] Λ := (AddMonoidHom.mk' l ladd).toIntLinearMap
  have lam_apply : ∀ x, lam x = l x := fun _ => rfl
  have hcont : ∀ x : Γ₀, ContinuousAt (S x) 0 := fun x =>
    ((hS x).1.differentiableAt (ball_mem_nhds _ one_pos)).continuousAt
  have hlamz : ∀ x, ∀ z ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0},
      ∃ w ∈ logCover h, expCover a w = z ∧ S x z = P w (lam x) := by
    intro x z hz
    obtain ⟨w, hw, rfl⟩ := exists_mem_logCover h hz
    exact ⟨w, hw, rfl, hl x w hw⟩
  have hinj : Function.Injective lam := by
    refine (injective_iff_map_eq_zero lam).2 fun x hx => ?_
    have h0 : S x 0 = (fun _ => 0 : (Fin n → ℂ) → (Fin g → ℂ)) 0 :=
      eq_at_zero_of_eqOn (a := a) (hcont x) continuousAt_const (fun z hz => by
        obtain ⟨w, hw, -, e⟩ := hlamz x z hz
        rw [e, hx, map_zero])
    exact Subtype.ext (by rw [← (hS x).2.1]; simpa using h0)
  have hsat : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ LinearMap.range lam → x ∈ LinearMap.range lam := by
    rintro k x hk ⟨y, hy⟩
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hval : ∀ z ∈ {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0},
        (k : ℂ)⁻¹ • S y z ∈ Γ z := by
      intro z hz
      obtain ⟨w, hw, rfl, e⟩ := hlamz y z hz
      have : (k : ℂ)⁻¹ • S y (expCover a w) = P w x := by
        rw [e, hy, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, inv_mul_cancel₀ hkc, one_smul]
      rw [this, ← (hP w hw).2.1]
      exact ⟨x, rfl⟩
    have hy0 : (k : ℂ)⁻¹ • (y : Fin g → ℂ) ∈ Γ₀ := by
      have hc : ContinuousAt (fun z => (k : ℂ)⁻¹ • S y z) 0 :=
        ContinuousAt.comp (g := fun v : Fin g → ℂ => (k : ℂ)⁻¹ • v)
          (continuous_const_smul _).continuousAt (hcont y)
      have := hlim (fun z => (k : ℂ)⁻¹ • S y z) hc hval
      simpa [(hS y).2.1] using this
    refine ⟨⟨_, hy0⟩, ?_⟩
    have hky : k • (⟨_, hy0⟩ : Γ₀) = y := by
      apply Subtype.ext
      change k • ((k : ℂ)⁻¹ • (y : Fin g → ℂ)) = y
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_inv_cancel₀ hkc, one_smul]
    apply smul_right_injective Λ hk
    change k • lam ⟨_, hy0⟩ = k • x
    rw [← map_zsmul, hky, hy]
  have hco := coiso_of_count E hbij halt lam hinj hsat (fun N hN => by
    obtain ⟨T', hcard, hdvd⟩ := hcount N hN
    refine ⟨T', by rw [hrank]; exact hcard, fun x y hx => ?_⟩
    obtain ⟨k, hk⟩ := hdvd x y hx _ (hmem w₀ hw₀)
    rw [hl x w₀ hw₀, hl y w₀ hw₀, (hP w₀ hw₀).2.2] at hk
    exact ⟨k, by exact_mod_cast hk⟩)
  let e : Γ₀ ≃ₗ[ℤ] LinearMap.range lam := LinearEquiv.ofInjective lam hinj
  have he : ∀ x : LinearMap.range lam, lam (e.symm x) = x := fun x => by
    have := congrArg Subtype.val (e.apply_symm_apply x)
    simpa [e] using this
  refine ⟨{ a_le := h, free := inferInstance, fin := inferInstance, rank := hrank, E := E, alt := halt,
            unimod := hbij, P := P, hol := hPhol, H := Hf,
            herm := fun w hw => (hpos _ (hmem w hw)).1,
            pos := fun w hw => (hpos _ (hmem w hw)).2,
            im := fun w hw => (hP w hw).2.2,
            T := fun i => (T i).toAddMonoidHom.toIntLinearMap,
            mono := fun i w hw x => hT i w hw x,
            W := LinearMap.range lam,
            coiso := fun x hx => ⟨1, one_ne_zero, by simpa using hco x hx⟩,
            s := fun x => S (e.symm x),
            s_hol := fun x => (hS _).1,
            s_eq := fun x w hw => by
              rw [hl _ w hw, ← lam_apply, he],
            span := ?_ }, rfl, fun w hw => (hP w hw).2.1⟩
  have hr : (Set.range fun x : LinearMap.range lam => S (e.symm x) 0) = (Γ₀ : Set (Fin g → ℂ)) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      simp only [(hS _).2.1]
      exact (e.symm x).2
    · intro hu
      refine ⟨e ⟨u, hu⟩, ?_⟩
      simp only [LinearEquiv.symm_apply_apply, (hS _).2.1]
  change Submodule.span ℂ (Set.range fun x : LinearMap.range lam => S (e.symm x) 0) = ⊤
  rw [hr]
  exact hspan

end GlobalTheory.CompanionTheory.Ar.Flat
