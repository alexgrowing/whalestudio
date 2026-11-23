import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ParametricIntegralSmoothness.IntCommute
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff

noncomputable section

namespace Formalism.MainStatements.RankOne.KD

open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm

section Cpt

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

def tr (a : Γ) : C(Γ, ℝ) →ₐ[ℝ] C(Γ, ℝ) := ContinuousMap.compRightAlgHom ℝ ℝ ⟨fun x => a * x, continuous_const.mul continuous_id⟩

def FinInv (V : Submodule ℝ C(Γ, ℝ)) : Prop := V.FG ∧ ∀ a : Γ, ∀ q ∈ V, tr a q ∈ V

def finAlg (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Subalgebra ℝ C(Γ, ℝ) where
  carrier := {p | ∃ V, FinInv V ∧ p ∈ V}
  mul_mem' := by
    rintro p q ⟨V, hV, hp⟩ ⟨W, hW, hq⟩
    refine ⟨V * W, ⟨hV.1.mul hW.1, fun a x hx => ?_⟩, Submodule.mul_mem_mul hp hq⟩
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) fun x y hx hy => ?_
    · rw [map_mul]; exact Submodule.mul_mem_mul (hV.2 a m hm) (hW.2 a n hn)
    · rw [map_add]; exact add_mem hx hy
  add_mem' := by
    rintro p q ⟨V, hV, hp⟩ ⟨W, hW, hq⟩
    refine ⟨V ⊔ W, ⟨hV.1.sup hW.1, fun a x hx => ?_⟩, Submodule.add_mem_sup hp hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]; exact Submodule.add_mem_sup (hV.2 a y hy) (hW.2 a z hz)
  algebraMap_mem' c := by
    refine ⟨Submodule.span ℝ {1}, ⟨Submodule.fg_span (finite_singleton _), fun a x hx => ?_⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, map_one]; exact hx
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]

theorem int_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure Γ) [IsFiniteMeasure μ] (p : C(Γ, ℝ))
    {F : Γ → V} (hF : Continuous F) : Integrable (fun x => p x • F x) μ :=
  (p.continuous.smul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem approx_id {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (μ : Measure Γ)
    [IsFiniteMeasure μ] [IsOpenPosMeasure μ] (A : Subalgebra ℝ C(Γ, ℝ)) (hA : A.SeparatesPoints) {ι : Type} [Fintype ι]
    {F : ι → Γ → V} (hF : ∀ i, Continuous (F i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p ∈ A, ∀ i, ‖F i 1 - ∫ x, p x • F i x ∂μ‖ < δ := by
  set U : Set Γ := ⋂ i, {x | ‖F i 1 - F i x‖ < δ / 2} with hU
  have hUo : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_lt (continuous_const.sub (hF i)).norm continuous_const
  have h1U : (1 : Γ) ∈ U := mem_iInter.2 fun i => by simpa using hδ
  obtain ⟨φ₀, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl (isClosed_singleton (x := (1 : Γ)))
    (disjoint_singleton_right.2 fun h => h h1U)
  have hc : 0 < ∫ x, φ₀ x ∂μ :=
    φ₀.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _)
      (fun x => (h01 x).1) (by rw [h1 rfl]; exact one_ne_zero)
  set φ : C(Γ, ℝ) := (∫ x, φ₀ x ∂μ)⁻¹ • φ₀ with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (inv_nonneg.2 hc.le) (h01 x).1
  have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hφ1 : ∫ x, φ x ∂μ = 1 := by
    simp only [hφ, ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hc.ne']
  have hM : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖F i x‖ ≤ M := fun i =>
    ⟨‖(⟨F i, hF i⟩ : C(Γ, V))‖, norm_nonneg _, fun x => (⟨F i, hF i⟩ : C(Γ, V)).norm_coe_le_norm x⟩
  choose M hM0 hM using hM
  set Mt : ℝ := (∑ i, M i) * μ.real univ + 1 with hMt
  have hMt0 : 0 < Mt := by
    have : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
    positivity
  obtain ⟨p, hp⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hA φ (δ / 2 / Mt)
    (by positivity)
  refine ⟨p, p.2, fun i => ?_⟩
  have e1 : F i 1 - ∫ x, φ x • F i x ∂μ = ∫ x, φ x • (F i 1 - F i x) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub (int_smul μ φ continuous_const) (int_smul μ φ (hF i)), integral_smul_const, hφ1, one_smul]
  have b1 : ‖F i 1 - ∫ x, φ x • F i x ∂μ‖ ≤ δ / 2 := by
    rw [e1]
    refine (norm_integral_le_of_norm_le (hφi.mul_const (δ / 2)) (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [norm_smul, Real.norm_of_nonneg (hφ0 x)]
      by_cases hx : x ∈ U
      · exact mul_le_mul_of_nonneg_left (mem_iInter.1 hx i).le (hφ0 x)
      · have : φ x = 0 := by simp [hφ, h0 hx]
        simp [this]
    · rw [integral_mul_const, hφ1, one_mul]
  have e2 : (∫ x, φ x • F i x ∂μ) - ∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ = ∫ x, (φ x - (p : C(Γ, ℝ)) x) • F i x ∂μ := by
    simp only [sub_smul]
    rw [integral_sub (int_smul μ φ (hF i)) (int_smul μ _ (hF i))]
  have b2 : ‖(∫ x, φ x • F i x ∂μ) - ∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ‖ ≤ ‖(p : C(Γ, ℝ)) - φ‖ * M i * μ.real univ := by
    rw [e2]
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_sub_rev]
    exact mul_le_mul (((p : C(Γ, ℝ)) - φ).norm_coe_le_norm x) (hM i x) (norm_nonneg _) (norm_nonneg _)
  have b3 : M i * μ.real univ ≤ Mt := by
    have : M i ≤ ∑ i, M i := Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ i)
    have := mul_le_mul_of_nonneg_right this (measureReal_nonneg (μ := μ) (s := univ))
    linarith
  have b4 : ‖(p : C(Γ, ℝ)) - φ‖ * M i * μ.real univ < δ / 2 := by
    rw [mul_assoc]
    calc _ ≤ ‖(p : C(Γ, ℝ)) - φ‖ * Mt := mul_le_mul_of_nonneg_left b3 (norm_nonneg _)
      _ < δ / 2 := (lt_div_iff₀ hMt0).1 hp
  have := norm_sub_le_norm_sub_add_norm_sub (F i 1) (∫ x, φ x • F i x ∂μ) (∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ)
  linarith

end Cpt

section Mat

variable {n : ℕ} {K : Set (Mat n)} {hK : IsMatGroup K}

def co (hK : IsMatGroup K) : (Mat n →L[ℝ] ℝ) →ₗ[ℝ] C(MG K hK, ℝ) where
  toFun f := ⟨fun x => f x.mat, f.continuous.comp MG.continuous_mat⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finAlg_sep : (finAlg (MG K hK)).SeparatesPoints := by
  intro x y hxy
  have hne : x.mat - y.mat ≠ 0 := fun h => hxy (MG.ext (sub_eq_zero.1 h))
  obtain ⟨i, j, hij⟩ : ∃ i j, x.mat i j ≠ y.mat i j := by
    by_contra h
    push Not at h
    exact hxy (MG.ext (Matrix.ext h))
  have hV : FinInv (LinearMap.range (co hK)) := by
    refine ⟨Submodule.fg_range _, ?_⟩
    rintro a _ ⟨f, rfl⟩
    exact ⟨f.comp (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a.mat)), rfl⟩
  let e : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun m => m i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hre : (x.mat i j).re = (y.mat i j).re
  · exact ⟨_, ⟨co hK (Complex.imCLM.comp e), ⟨_, hV, ⟨_, rfl⟩⟩, rfl⟩, fun h => hij (Complex.ext hre h)⟩
  · exact ⟨_, ⟨co hK (Complex.reCLM.comp e), ⟨_, hV, ⟨_, rfl⟩⟩, rfl⟩, hre⟩

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {G : Set (Mat n)}
  {σ : Mat n → (H →L[ℂ] H)} [CompactSpace (MG K hK)]

theorem dsW_int (hG : IsMatGroup G) (hKG : K ⊆ G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (μ : Measure (MG K hK))
    [IsFiniteMeasure μ] (p : C(MG K hK, ℝ)) : ∀ {W : List (Mat n)}, LieW G W →
    dsW σ W (∫ g, p g • σ g.mat v ∂μ) = ∫ g, p g • dsW σ W (σ g.mat v) ∂μ
  | [], _ => rfl
  | X :: W, hXW => by
    have hW : LieW G W := fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)
    have hX := hXW X List.mem_cons_self
    have hj : Continuous fun g : MG K hK => MG.mk hG g.mat (hKG g.mem) := MG.continuous_iff.2 MG.continuous_mat
    have c1 : Continuous fun g : MG K hK => dsW σ W (σ g.mat v) := (continuous_orbit (hG := hG) h hv hW).comp hj
    have c2 : ∀ {W' : List (Mat n)}, LieW G W' →
        Continuous fun q : ℝ × MG K hK => σ (ex X q.1) (dsW σ W' (σ q.2.mat v)) := fun hW' =>
      (continuous_orbit₂ (hG := hG) h hv hW' hX).comp (continuous_fst.prodMk (hj.comp continuous_snd))
    rw [dsW_cons, dsW_int hG hKG h hv μ p hW]
    have e : ∀ t, σ (ex X t) (∫ g, p g • dsW σ W (σ g.mat v) ∂μ) =
        ∫ g, p g • σ (ex X t) (dsW σ W (σ g.mat v)) ∂μ := fun t => by
      rw [← (σ (ex X t)).integral_comp_comm (int_smul μ p c1)]
      simp only [ContinuousLinearMap.map_smul_of_tower]
    have := hasDerivAt_integral_cpt (μ := μ)
      (F := fun t g => p g • σ (ex X t) (dsW σ W (σ g.mat v)))
      (F' := fun t g => p g • σ (ex X t) (dsW σ (X :: W) (σ g.mat v)))
      (fun t => p.continuous.smul ((c2 hW).comp (Continuous.prodMk_right t)))
      ((p.continuous.comp continuous_snd).smul (c2 hXW))
      (fun t a => (((hv.apply h (hKG a.mem)).dsW h hW).hasDerivAt h hX t).fun_const_smul _)
      isCompact_univ (fun a ha => absurd (mem_univ a) ha) (fun t _ a ha => absurd (mem_univ a) ha)
    unfold ds
    simp_rw [e]
    rw [this.deriv]
    simp [ex_zero, h.map_one]

theorem fin_of_finAlg (hG : IsMatGroup G) (hKG : K ⊆ G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v)
    {p : C(MG K hK, ℝ)} (hp : p ∈ finAlg (MG K hK)) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ (∫ g, p g • σ g.mat v ∂haar) ∈ S ∧ ∀ a ∈ K, ∀ x ∈ S, σ a x ∈ S := by
  obtain ⟨V, ⟨⟨s, hs⟩, hinv⟩, hpV⟩ := hp
  have hj : Continuous fun g : MG K hK => MG.mk hG g.mat (hKG g.mem) := MG.continuous_iff.2 MG.continuous_mat
  have c1 : Continuous fun g : MG K hK => σ g.mat v :=
    (continuous_orbit (hG := hG) (W := []) h hv fun _ hX => absurd hX List.not_mem_nil).comp hj
  let T : C(MG K hK, ℝ) →ₗ[ℝ] H :=
    { toFun := fun q => ∫ g, q g • σ g.mat v ∂haar
      map_add' := fun q q' => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (int_smul _ q c1) (int_smul _ q' c1)
      map_smul' := fun c q => by
        simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
        exact integral_smul _ _ }
  have hS : Submodule.span ℂ (V.map T : Set H) = Submodule.span ℂ (T '' s) := by
    rw [← hs, Submodule.map_span, Submodule.span_span_of_tower]
  refine ⟨Submodule.span ℂ (V.map T : Set H), ?_, Submodule.subset_span ⟨p, hpV, rfl⟩, fun a ha x hx => ?_⟩
  · rw [hS]; exact FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image _)
  · refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun c y _ hy => by rw [map_smul]; exact Submodule.smul_mem _ c hy) hx
    obtain ⟨q, hq, rfl⟩ := hy
    set a' : MG K hK := MG.mk hK a ha with ha'
    refine Submodule.subset_span ⟨tr a'⁻¹ q, hinv _ q hq, ?_⟩
    show ∫ g, q (a'⁻¹ * g) • σ g.mat v ∂haar = σ a (∫ g, q g • σ g.mat v ∂haar)
    rw [← (σ a).integral_comp_comm (int_smul _ q c1),
      ← integral_mul_left_eq_self (fun g : MG K hK => q (a'⁻¹ * g) • σ g.mat v) a']
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [inv_mul_cancel_left, ContinuousLinearMap.map_smul_of_tower]
    congr 1
    exact h.apply_mul (hKG ha) (hKG g.mem) v

end Mat

open PI.UpqRep in
theorem kDense (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (v : H)
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (Ws : List (List (Mat (2 * r + k + 1))))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) (e : ℝ) (he : 0 < e) :
    ∃ v' : H, IsKFinHpk (k := k) (r := r) σ v' ∧ (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (v - v')‖).sum < e := by
  have hKS := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, -, -⟩, -, -⟩ := hσ
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have h : RepOn (UH (Hpk k r)) σ := repOn_of_conj hP hPJ h1 hm
  set K : Set (Mat (2 * r + k + 1)) := UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) with hKd
  have hUc : IsCompact (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat (2 * r + k + 1))) := by
    have hcl : IsClosed (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat (2 * r + k + 1))) := by
      have : (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat (2 * r + k + 1))) = {a | a * aᴴ = 1} := by
        ext a; exact Matrix.mem_unitaryGroup_iff
      rw [this]
      exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
    have hb : IsCompact (Set.pi univ fun _ : Fin (2 * r + k + 1) => Set.pi univ fun _ : Fin (2 * r + k + 1) =>
        Metric.closedBall (0 : ℂ) 1) := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    exact hb.of_isClosed_subset hcl fun a ha i _ j _ => by
      simpa using entry_norm_bound_of_unitary ha i j
  have hK : IsMatGroup K := by
    refine ⟨hG.1.inter hUc.isClosed, ⟨hG.2.1, one_mem _⟩, fun a ha b hb => ⟨hG.2.2.1 a ha.1 b hb.1, mul_mem ha.2 hb.2⟩,
      fun a ha => ⟨⟨(hG.2.2.2 a ha.1).1, ?_⟩, (hG.2.2.2 a ha.1).2⟩⟩
    rw [Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 ha.2)]
    exact Unitary.star_mem ha.2
  have hKc : IsCompact K := hUc.inter_left hG.1
  have : CompactSpace (MG K hK) := isCompact_iff_compactSpace.1 hKc
  have : T2Space (MG K hK) := MG.isClosedEmbedding_mat.isEmbedding.t2Space
  have hL : (0 : ℝ) < Ws.length + 1 := by positivity
  have hW : ∀ i : Fin Ws.length, LieW (UH (Hpk k r)) (Ws.get i) :=
    fun i X hX t => ex_mem_of_lie (hWs _ (List.get_mem _ _) X hX) t
  have hj : Continuous fun g : MG K hK => MG.mk hG g.mat g.mem.1 := MG.continuous_iff.2 MG.continuous_mat
  obtain ⟨p, hp, hb⟩ := approx_id (haar : Measure (MG K hK)) _ finAlg_sep
    (F := fun (i : Fin Ws.length) (g : MG K hK) => dsW σ (Ws.get i) (σ g.mat v))
    (fun i => (continuous_orbit (hG := hG) h hv (hW i)).comp hj) (div_pos he hL)
  have hfin : IsKFinHpk (k := k) (r := r) σ (∫ g : MG K hK, p g • σ g.mat v ∂haar) :=
    fin_of_finAlg hG inter_subset_left h hv hp
  refine ⟨_, hfin, ?_⟩
  have hle := List.sum_le_card_nsmul
    (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (v - ∫ g : MG K hK, p g • σ g.mat v ∂haar)‖) (e / (Ws.length + 1)) (by
      intro t ht
      obtain ⟨W, hW', rfl⟩ := List.mem_map.1 ht
      obtain ⟨i, rfl⟩ := List.get_of_mem hW'
      rw [dsigW_eq', dsW_sub h hv (hKS _ hfin) (hW i), dsW_int hG inter_subset_left h hv _ p (hW i)]
      have := (hb i).le
      have e1 : σ (1 : MG K hK).mat v = v := by
        show σ 1 v = v
        rw [h.map_one]; rfl
      simp only [e1] at this
      exact this)
  refine hle.trans_lt ?_
  rw [List.length_map, nsmul_eq_mul, ← mul_div_assoc, div_lt_iff₀ hL]
  nlinarith

end Formalism.MainStatements.RankOne.KD
