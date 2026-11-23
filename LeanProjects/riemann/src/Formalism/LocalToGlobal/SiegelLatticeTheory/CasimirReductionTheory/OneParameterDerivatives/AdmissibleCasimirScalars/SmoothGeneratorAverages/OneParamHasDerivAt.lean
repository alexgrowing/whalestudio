import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted.SkewDerivative

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem oneParam_hasDerivAt (φ : ℝ → E →L[ℂ] E) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t)
    (hc : Continuous φ) : ∃ A : E →L[ℂ] E, HasDerivAt φ A 0 := by
  set ψ : ℝ → (E →L[ℂ] E) := fun t => ∫ s in (0 : ℝ)..t, φ s with hψdef
  have hψ : ∀ t, HasDerivAt ψ (φ t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hψ0 : ψ 0 = 0 := intervalIntegral.integral_same
  have key : ∀ t d : ℝ, φ t * ψ d = ψ (t + d) - ψ t := by
    intro t d
    have h1 : φ t * ψ d = ∫ s in (0 : ℝ)..d, φ t * φ s :=
      ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable 0 d)).symm
    rw [h1]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left φ t, add_zero, hψdef]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hs := hasDerivAt_iff_tendsto_slope.mp (hψ 0)
  rw [h0] at hs
  have hev : ∀ᶠ d in nhdsWithin (0 : ℝ) {0}ᶜ, IsUnit (slope ψ 0 d) ∧ d ∈ ({0}ᶜ : Set ℝ) :=
    (hs.eventually_mem (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin
  obtain ⟨δ, hδu, hδ0⟩ := hev.exists
  have hδ0' : δ ≠ 0 := hδ0
  obtain ⟨u, hu⟩ := hδu
  have hψδ : ψ δ = δ • (u : E →L[ℂ] E) := by
    rw [hu, slope_def_module, hψ0, sub_zero, sub_zero, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  have e : φ = fun t => δ⁻¹ • (ψ (t + δ) - ψ t) * ((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) := by
    funext t
    have h2 := key t δ
    rw [hψδ, mul_smul_comm] at h2
    rw [← h2, smul_smul, inv_mul_cancel₀ hδ0', one_smul, mul_assoc, Units.mul_inv, mul_one]
  have hD : HasDerivAt (fun t => ψ (t + δ) - ψ t) (φ (0 + δ) - φ 0) 0 :=
    (HasDerivAt.comp_add_const 0 δ (hψ (0 + δ))).sub (hψ 0)
  rw [e]
  exact ⟨_, (hD.const_smul δ⁻¹).mul_const _⟩

theorem clm_der {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : F →L[ℂ] G) {f : ℝ → F} {f' : F} (hf : HasDerivAt f f' 0) : HasDerivAt (fun t => L (f t)) (L f') 0 :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf

theorem apply_der {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    {φ : ℝ → F →L[ℂ] G} {A : F →L[ℂ] G} (hA : HasDerivAt φ A 0) (x : F) :
    HasDerivAt (fun t => φ t x) (A x) 0 := clm_der (ContinuousLinearMap.apply ℂ G x) hA

end Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Orth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sq_sum_orth {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → H)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i, x j⟫_ℂ = 0) : ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := by
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have h0 : ⟪x a, ∑ i ∈ s, x i⟫_ℂ = 0 := by
    rw [inner_sum]
    exact Finset.sum_eq_zero fun i hi => h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
      (fun e => ha (by rw [e]; exact hi))
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [← ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
  simp only [sq]
  exact h2

end Orth

section Gens

variable {n : ℕ} {ε : Fin n → Bool}

theorem gen_inK (p : Fin n × Fin n) (hp : ε p.1 = ε p.2) : inK ε (gen ε p) := by
  obtain ⟨a, b⟩ := p
  simp only at hp
  rw [Formalism.REAL.f1alg_inK_iff]
  have hsg : ((sg ε (a, b) : ℝ) : ℂ) = 1 := by simp [sg, hp]
  have hc : ∀ i j : Fin n, ε i = ε j → Matrix.single i j (1 : ℂ) * Jm ε = Jm ε * Matrix.single i j 1 := by
    intro i j hij
    ext k l
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h : i = k ∧ j = l
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      rw [hij]
      ring
    · rw [if_neg h]
      ring
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold gen
  dsimp only
  simp only [hsg, one_smul]
  split_ifs with h1 h2
  · constructor
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, hI, neg_smul]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hc a a rfl]
  · constructor
    · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, neg_sub]
    · rw [Matrix.sub_mul, Matrix.mul_sub, hc a b hp, hc b a hp.symm]
  · constructor
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single,
        Matrix.conjTranspose_single, star_one, hI, neg_smul, add_comm (Matrix.single a b (1 : ℂ))]
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hc a b hp, hc b a hp.symm]

theorem exp_mem_Kset (p : Fin n × Fin n) (hp : ε p.1 = ε p.2) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • gen ε p) ∈ Kset ε := by
  exact (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (Formalism.REAL.inK_smul_real ε (gen_inK p hp) t)

end Gens

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
  (p : Fin n × Fin n) (hp : ε p.1 = ε p.2)

include hσ hp in
theorem U_mem (t : ℝ) : NormedSpace.exp ((t : ℂ) • gen ε p) ∈ UJset ε := (Formalism.REAL.maximal_compact_facts n ε).1 _ (exp_mem_Kset p hp t)

include hσ hp in
theorem U_zero (v : H) : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • gen ε p)) v = v := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply]

include hσ hp in
theorem U_add (s t : ℝ) (v : H) : σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • gen ε p)) v =
    σ (NormedSpace.exp ((s : ℂ) • gen ε p)) (σ (NormedSpace.exp ((t : ℂ) • gen ε p)) v) := by
  have e : (((s + t : ℝ) : ℂ) • gen ε p) = (s : ℂ) • gen ε p + (t : ℂ) • gen ε p := by
    push_cast
    rw [add_smul]
  rw [e, Matrix.exp_add_of_commute _ _ (((Commute.refl (gen ε p)).smul_left (s : ℂ)).smul_right (t : ℂ)),
    hσ.1.2 _ (U_mem σ hσ p hp s) _ (U_mem σ hσ p hp t)]
  rfl

include hσ hp in
theorem U_inner (t : ℝ) (u w : H) : ⟪σ (NormedSpace.exp ((t : ℂ) • gen ε p)) u,
    σ (NormedSpace.exp ((t : ℂ) • gen ε p)) w⟫_ℂ = ⟪u, w⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (σ (NormedSpace.exp ((t : ℂ) • gen ε p)) : H →ₗ[ℂ] H)
      norm_map' := hσ.2.1 _ (U_mem σ hσ p hp t) }
  exact L.inner_map_map u w

include hσ hp in
theorem U_cont (v : H) : Continuous fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) v := by
  have hc : Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • gen ε p) := by
    have hE := (Formalism.REAL.group_exponential_facts n ε (gen ε p) (gen_inK p hp).1).2.2.1
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • gen ε p)) =
        fun t => Formalism.REAL.toM (Formalism.REAL.expG ε (gen ε p) t) := by
      funext t
      rw [Formalism.REAL.toM_expG ε _ t (gen_inK p hp).1]
    rw [e]
    exact Units.continuous_val.comp (continuous_subtype_val.comp hE)
  exact (hσ.2.2 v).comp_continuous hc (fun t => U_mem σ hσ p hp t)

include hσ hp in

theorem skew_of_der {u w u' w' : H}
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) u) u' 0)
    (hw : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) w) w' 0) :
    ⟪u, w'⟫_ℂ + ⟪u', w⟫_ℂ = 0 := by
  have h1 := hu.inner ℂ hw
  have h2 : HasDerivAt (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • gen ε p)) u,
      σ (NormedSpace.exp ((t : ℂ) • gen ε p)) w⟫_ℂ) 0 0 := by
    simp only [U_inner σ hσ p hp]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  simpa only [U_zero σ hσ p hp] using h3

omit hσ p hp in

def Ev (X : Matrix (Fin n) (Fin n) ℂ) (μ : ℝ) : Submodule ℂ H where
  carrier := {u | HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) u) (((μ : ℂ) * Complex.I) • u) 0}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, smul_zero]
    exact hasDerivAt_const _ _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, smul_add] at *
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, map_smul] at *
    rw [smul_comm]
    exact ha.const_smul c

include hσ hp in
theorem Ev_orth {μ ν : ℝ} (hne : μ ≠ ν) {u w : H} (hu : u ∈ Ev σ (gen ε p) μ) (hw : w ∈ Ev σ (gen ε p) ν) :
    ⟪u, w⟫_ℂ = 0 := by
  have h := skew_of_der σ hσ p hp hu hw
  rw [inner_smul_right, inner_smul_left] at h
  have hc : (starRingEnd ℂ) ((μ : ℂ) * Complex.I) = -((μ : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal]
  rw [hc, ← add_mul] at h
  have hne' : ((ν : ℂ) * Complex.I + -((μ : ℂ) * Complex.I)) ≠ 0 := by
    intro h0
    apply hne
    have h5 := congrArg Complex.im h0
    simp at h5
    linarith
  exact (mul_eq_zero.mp h).resolve_left hne'

include hσ hp in

theorem bound_on_sup (Λ : Finset ℝ) (v : H) (hv : v ∈ ⨆ μ ∈ Λ, Ev σ (gen ε p) μ) :
    ‖dS σ (gen ε p) v‖ ≤ (∑ μ ∈ Λ, |μ|) * ‖v‖ := by
  obtain ⟨c, hc⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ v).mp hv
  have hder : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) v)
      (∑ μ ∈ Λ, ((μ : ℂ) * Complex.I) • (c μ : H)) 0 := by
    rw [← hc]
    simp only [map_sum]
    exact HasDerivAt.fun_sum fun μ _ => (c μ).2
  have hpy : ‖v‖ ^ 2 = ∑ μ ∈ Λ, ‖(c μ : H)‖ ^ 2 := by
    rw [← hc]
    exact norm_sq_sum_orth Λ (fun μ => (c μ : H)) (fun i _ j _ hij => Ev_orth σ hσ p hp hij (c i).2 (c j).2)
  have hle : ∀ μ ∈ Λ, ‖(c μ : H)‖ ≤ ‖v‖ := by
    intro μ hμ
    have h4 : ‖(c μ : H)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [hpy]
      exact Finset.single_le_sum (f := fun μ => ‖(c μ : H)‖ ^ 2) (fun i _ => sq_nonneg _) hμ
    nlinarith [norm_nonneg (c μ : H), norm_nonneg v]
  show ‖deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) v) 0‖ ≤ _
  rw [hder.deriv]
  calc ‖∑ μ ∈ Λ, ((μ : ℂ) * Complex.I) • (c μ : H)‖ ≤ ∑ μ ∈ Λ, ‖((μ : ℂ) * Complex.I) • (c μ : H)‖ :=
        norm_sum_le _ _
    _ = ∑ μ ∈ Λ, |μ| * ‖(c μ : H)‖ := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ μ ∈ Λ, |μ| * ‖v‖ := Finset.sum_le_sum fun μ hμ => mul_le_mul_of_nonneg_left (hle μ hμ) (abs_nonneg μ)
    _ = (∑ μ ∈ Λ, |μ|) * ‖v‖ := (Finset.sum_mul _ _ _).symm

include hσ hp in

theorem isoK_le (S : Submodule ℂ H) (hfd : FiniteDimensional ℂ S) (hst : IsKStableOn ε σ S) :
    ∃ Λ : Finset ℝ, isoK ε σ S ≤ ⨆ μ ∈ Λ, Ev σ (gen ε p) μ := by
  haveI := hfd
  have hKmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • gen ε p) ∈ Formalism.REAL.Kset ε := exp_mem_Kset p hp
  let φ : ℝ → (S →L[ℂ] S) := fun t =>
    LinearMap.toContinuousLinearMap
      (((σ (NormedSpace.exp ((t : ℂ) • gen ε p)) : H →ₗ[ℂ] H).restrict
        (p := S) (q := S) (fun v hv => hst _ (hKmem t) v hv)))
  have hφ : ∀ (t : ℝ) (v : S), ((φ t v : S) : H) = σ (NormedSpace.exp ((t : ℂ) • gen ε p)) v :=
    fun t v => rfl
  have h0 : φ 0 = 1 := ContinuousLinearMap.ext fun v => Subtype.ext (by
    rw [hφ]
    exact U_zero σ hσ p hp v)
  have hadd : ∀ s t, φ (s + t) = φ s * φ t := fun s t =>
    ContinuousLinearMap.ext fun v => Subtype.ext (by
      rw [hφ]
      exact U_add σ hσ p hp s t v)
  have hcont : Continuous φ := by
    rw [continuous_clm_apply]
    intro v
    exact (U_cont σ hσ p hp (v : H)).subtype_mk _
  obtain ⟨A, hA⟩ := oneParam_hasDerivAt φ h0 hadd hcont
  have hder : ∀ v : S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) (v : H))
      ((A v : S) : H) 0 := fun v => clm_der S.subtypeL (apply_der hA v)
  have hskew : ∀ v w : S, ⟪(v : H), ((A w : S) : H)⟫_ℂ + ⟪((A v : S) : H), (w : H)⟫_ℂ = 0 :=
    fun v w => skew_of_der σ hσ p hp (hder v) (hder w)
  let B : S →ₗ[ℂ] S := (((-Complex.I) • A : S →L[ℂ] S) : S →ₗ[ℂ] S)
  have hB : B.IsSymmetric := by
    intro x y
    show ⟪((-Complex.I) • A x : S), y⟫_ℂ = ⟪x, ((-Complex.I) • A y : S)⟫_ℂ
    rw [inner_smul_left, inner_smul_right, Submodule.coe_inner, Submodule.coe_inner]
    rw [show ⟪(x : H), ((A y : S) : H)⟫_ℂ = -⟪((A x : S) : H), (y : H)⟫_ℂ from
      eq_neg_of_add_eq_zero_left (hskew x y)]
    rw [map_neg, Complex.conj_I]
    ring
  have hbA : ∀ i, (A (hB.eigenvectorBasis rfl i) : S) =
      (((hB.eigenvalues rfl i : ℝ) : ℂ) * Complex.I) • hB.eigenvectorBasis rfl i := by
    intro i
    have h1 := hB.apply_eigenvectorBasis rfl i
    have h2 : (A (hB.eigenvectorBasis rfl i) : S) = Complex.I • B (hB.eigenvectorBasis rfl i) := by
      show _ = Complex.I • ((-Complex.I) • A (hB.eigenvectorBasis rfl i))
      rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    rw [h2, h1, smul_smul, mul_comm]
    rfl
  have hmemΛ : ∀ i, Ev σ (gen ε p) (hB.eigenvalues rfl i) ≤
      ⨆ μ ∈ Finset.univ.image (hB.eigenvalues rfl), Ev σ (gen ε p) μ := fun i =>
    le_biSup (fun μ => Ev σ (gen ε p) μ) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hG : Formalism.REAL.inG ε (gen ε p) := (gen_inK p hp).1
  have hexpK : ∀ t : ℝ, Formalism.REAL.toMK (Formalism.REAL.expK ε (gen ε p) t) =
      NormedSpace.exp ((t : ℂ) • gen ε p) := by
    intro t
    show Formalism.REAL.toM ((Formalism.REAL.expK ε (gen ε p) t : Formalism.REAL.KG ε) : Formalism.REAL.UJ ε) = _
    rw [((Formalism.REAL.group_exponential_facts n ε (gen ε p) hG).2.2.2 (gen_inK p hp)).1 t,
      Formalism.REAL.toM_expG ε (gen ε p) t hG]
  refine ⟨Finset.univ.image (hB.eigenvalues rfl), ?_⟩
  show sSup _ ≤ _
  refine sSup_le ?_
  rintro S' ⟨Θ, hΘ, rfl⟩
  have hΘEv : ∀ i, Θ (hB.eigenvectorBasis rfl i) ∈ Ev σ (gen ε p) (hB.eigenvalues rfl i) := by
    intro i
    have horb : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) (Θ (hB.eigenvectorBasis rfl i))) =
        fun t => (LinearMap.toContinuousLinearMap Θ) (φ t (hB.eigenvectorBasis rfl i)) := by
      funext t
      have h3 := hΘ (Formalism.REAL.expK ε (gen ε p) t) (hB.eigenvectorBasis rfl i) (φ t (hB.eigenvectorBasis rfl i))
        (by
          show _ = σ (Formalism.REAL.toMK (Formalism.REAL.expK ε (gen ε p) t)) _
          rw [hexpK t]
          rfl)
      simp only [hexpK t] at h3
      show _ = Θ (φ t (hB.eigenvectorBasis rfl i))
      rw [h3]
    show HasDerivAt _ _ 0
    rw [horb]
    have h4 := clm_der (LinearMap.toContinuousLinearMap Θ) (apply_der hA (hB.eigenvectorBasis rfl i))
    rw [hbA i, map_smul] at h4
    exact h4
  rintro _ ⟨v, rfl⟩
  rw [← (hB.eigenvectorBasis rfl).sum_repr v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hmemΛ i (hΘEv i))

include hσ hp in
theorem bound_one (S : Submodule ℂ H) (hfd : FiniteDimensional ℂ S) (hst : IsKStableOn ε σ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ isoK ε σ S, ‖dS σ (gen ε p) v‖ ≤ C * ‖v‖ := by
  obtain ⟨Λ, hΛ⟩ := isoK_le σ hσ p hp S hfd hst
  exact ⟨∑ μ ∈ Λ, |μ|, Finset.sum_nonneg fun μ _ => abs_nonneg μ,
    fun v hv => bound_on_sup σ hσ p hp Λ v (hΛ hv)⟩

end Main

end Formalism.L2.SG.Pf.admitted.SkewDerivative

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

theorem c5 : CompactDerivativesBounded := by
  intro n ε H _ _ _ σ hσ S hfd hst
  have hb : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ v ∈ isoK ε σ S, ‖dS σ (gen ε p) v‖ ≤ C * ‖v‖ :=
    fun p hp => SkewDerivative.bound_one σ hσ p hp S hfd hst
  choose! C hC0 hC using hb
  refine ⟨∑ q, max (C q) 0, fun p hp v hv => (hC p hp v hv).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))⟩
  exact (le_max_left _ _).trans
    (Finset.single_le_sum (f := fun q => max (C q) 0) (fun q _ => le_max_right _ _) (Finset.mem_univ p))

end Formalism.L2.SG.Pf.admitted
