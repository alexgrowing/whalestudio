import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpanStatement

noncomputable section
namespace LevelTowerAlt

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem limit_strong : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ (W : Submodule (𝓞 E) Λ) (I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (Hb M : Matrix (Fin g) (Fin g) ℂ) (u : Λ →ₗ[ℤ] (Fin g → ℤ)), (∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0) ∧ IsSaturated I ∧ Function.Injective per ∧ (∀ (c : 𝓞 E) (x : W), per (c • x) = L.B 0 c (per x)) ∧ M.det ≠ 0 ∧ (∀ x : W, (x : Λ) ∈ I → per x = M *ᵥ cst (u x)) ∧ ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b hσ hb
  classical
  obtain ⟨bas, A, T0, B, c, ρ, h⟩ := exists_isChart L.toLogPeriods
  obtain ⟨Pr, hPr⟩ := GlobalTheory.T.exists_isKerProj' g (∑ j, B j)
  obtain ⟨hsat, hs, hinj, hspan⟩ := GlobalTheory.T.chartW_saturated_and_continuous_section n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hext, hlim⟩ := GlobalTheory.T.mem_chartW_of_continuous_period n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hHerm, hIm, hKill, hPos⟩ := GlobalTheory.T.chartQ_hermitian_and_real_pairing n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  obtain ⟨hQc, ρ', hρ', hrep⟩ := GlobalTheory.T.chartQ_continuousAt_and_local_solution n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos

  have hBc : ∀ (c' : 𝓞 E) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 →
      ContinuousAt (fun z => L.B z c' (t z)) 0 := fun c' t ht => contAt_act L c' t ht
  have hstab : ∀ (c' : 𝓞 E) (x : Λ), x ∈ chartW bas B → c' • x ∈ chartW bas B := by
    intro c' x hx
    refine hext (c' • x) (fun z => L.B z c' (chartS bas A T0 x z)) (hBc c' _ (hs x hx).1) fun w hw => ?_
    rw [L.act w hw, (hs x hx).2 w hw]
  have hconj : ∀ c' : 𝓞 E, ∃ c'' : 𝓞 E, (c'' : E) = IsCMField.complexConj E (c' : E) := by
    intro c'
    refine ⟨⟨IsCMField.complexConj E (c' : E), ?_⟩, rfl⟩
    exact (NumberField.RingOfIntegers.isIntegral_coe c').map (IsCMField.complexConj E)
  let W : Submodule (𝓞 E) Λ :=
    { carrier := chartW bas B
      add_mem' := fun hx hy => (chartW bas B).add_mem hx hy
      zero_mem' := (chartW bas B).zero_mem
      smul_mem' := fun c' x hx => hstab c' x hx }
  have hW : ∀ x, x ∈ W ↔ x ∈ chartW bas B := fun x => Iff.rfl
  let I : Submodule (𝓞 E) Λ :=
    { carrier := {x | x ∈ chartW bas B ∧ ∀ y ∈ chartW bas B, L.toLogPeriods.E x y = 0}
      add_mem' := fun {x y} hx hy => ⟨(chartW bas B).add_mem hx.1 hy.1, fun u hu => by
        rw [map_add, LinearMap.add_apply, hx.2 u hu, hy.2 u hu, add_zero]⟩
      zero_mem' := ⟨(chartW bas B).zero_mem, fun u _ => by simp⟩
      smul_mem' := fun c' x hx => ⟨hstab c' x hx.1, fun u hu => by
        obtain ⟨c'', hc⟩ := hconj c'
        rw [L.adj c' c'' hc]
        exact hx.2 _ (hstab c'' u hu)⟩ }
  have hI : ∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0 := fun x => Iff.rfl
  let toZ : W →+ chartW bas B := AddMonoidHom.mk' (fun x => ⟨x.1, x.2⟩) (fun _ _ => rfl)
  have hrad : ∀ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ↔ (x : Λ) ∈ I :=
    fun x => ⟨fun hx => ⟨x.2, fun y hy => hx ⟨y, hy⟩⟩, fun hx x' => hx.2 _ x'.2⟩
  let per : W →+ (Fin g → ℂ) := (chartPer bas A T0 B).comp toZ
  have hper : ∀ x : W, per x = chartS bas A T0 (x : Λ) 0 := fun _ => rfl
  let s : W → (Fin n → ℂ) → Fin g → ℂ := fun x => chartS bas A T0 (x : Λ)
  have hs' : ∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x :=
    fun x => ⟨(hs x.1 x.2).1, rfl, (hs x.1 x.2).2⟩
  have hinj' : Function.Injective per := fun x y hxy => Subtype.ext (congrArg Subtype.val (hinj hxy))
  have hseq : ∃ ws : ℕ → Fin n → ℂ, (∀ m, ws m ∈ logCover L.a_le) ∧
      Tendsto (fun m => expCover a (ws m)) atTop (𝓝 0) := by
    refine ⟨fun m k => if k.val < a then -(((m : ℝ) + 1 : ℝ) : ℂ) else 0, fun m => ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hi, if_true, Complex.neg_re, Complex.ofReal_re]
      linarith
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp [hk']
    · rw [tendsto_pi_nhds]
      intro k
      by_cases hk : k.val < a
      · simp only [expCover, hk, if_true, Pi.zero_apply]
        have h1 : Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) + 1))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using h2
      · simp [expCover, hk]
  have hact : ∀ (c' : 𝓞 E) (x : W), per (c' • x) = L.B 0 c' (per x) := by
    intro c' x
    obtain ⟨ws, hws, hlim0⟩ := hseq
    have h1 : Tendsto (fun m => chartS bas A T0 ((c' • x : W) : Λ) (expCover a (ws m))) atTop
        (𝓝 (per (c' • x))) := (hs' (c' • x)).1.tendsto.comp hlim0 |>.congr fun _ => rfl
    have h2 : Tendsto (fun m => L.B (expCover a (ws m)) c' (chartS bas A T0 (x : Λ) (expCover a (ws m)))) atTop
        (𝓝 (L.B 0 c' (per x))) := (hBc c' _ (hs' x).1).tendsto.comp hlim0 |>.congr fun _ => rfl
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    rw [(hs x.1 x.2).2 _ (hws m), ← L.act _ (hws m)]
    exact ((hs _ (hstab c' x.1 x.2)).2 _ (hws m)).symm
  have hset : {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ∧ p = chartPer bas A T0 B x} =
      {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad x).1 hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad ⟨x.1, x.2⟩).2 hx, rfl⟩
  refine ⟨W, I, per, chartQ Pr A T0 0, (A 0)ᵀ, uCo bas, hI, ?_, hinj', hact, by rw [det_transpose]; exact h.A_det, ?_, ?_⟩
  · intro x k hk hx
    have h2 : x ∈ chartW bas B := hsat x k hk hx.1
    refine ⟨h2, fun y hy => ?_⟩
    have h3 := hx.2 y hy
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hk
  · intro x hx
    have hv : vCo bas (x : Λ) = 0 := by
      funext i
      have hv0 : vCo bas (bas (.inl i)) = 0 := by
        funext j
        simp [vCo]
      have hu0 : uCo bas (bas (.inl i)) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [uCo]
        · simp [uCo, hj, Finsupp.single_apply, Ne.symm hj]
      have h1 := hx.2 (bas (.inl i)) (by simp [chartW, hv0])
      rw [form_coords bas _ h.form L.alt, hv0, hu0] at h1
      simpa using h1
    rw [hper, chartS, hv]
    congr 1
    funext k
    simp [cst, mulVec, dotProduct]
  · refine limit_of_data E n a g Λ Ψ L σ m b W I per s (chartQ Pr A T0 0) (chartQ Pr A T0) ρ' hσ hb (fun x hx => hx.1)
      (fun x hx y hy => hx.2 y hy.1) hinj' hact hs' hHerm ?_ hQc rfl hρ' ?_
    · intro v
      rw [← hset]
      exact hPos v
    · intro w hw hwρ y
      obtain ⟨p, h1, h2, h3⟩ := hrep w hw hwρ y
      refine ⟨p, ?_, fun x hx => ?_, h3⟩
      · refine Submodule.span_mono ?_ h1
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, (hrad x).1 hx, rfl⟩
      · exact h2 ⟨x, hx.1⟩ ((hrad ⟨x, hx.1⟩).2 hx)

theorem eig_indep {E : Type} [Field E] [NumberField E] {g r : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {W I : Submodule (𝓞 E) Λ} (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (u : Λ →ₗ[ℤ] (Fin g → ℤ)) (hinj : Function.Injective per)
    (hact : ∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) (hM : M.det ≠ 0)
    (hu : ∀ x : W, (x : Λ) ∈ I → per x = M *ᵥ cst (u x)) (y : Fin r → W) (hy : ∀ a, (y a : Λ) ∈ I)
    (hli : LinearIndependent (𝓞 E) y) (s : 𝓞 E →+* ℂ) {x₀ : Fin g → ℂ} (hx₀ : x₀ ∈ eigSp ρ s) (h0 : x₀ ≠ 0) :
    LinearIndependent ℂ fun a => eigComp ρ s (per (y a)) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eigenComponent_polynomial E s
  obtain ⟨hc1, -, hc3⟩ := hc _ ρ
  let e := RingOfIntegers.basis E
  let γ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun k => ∑ x ∈ c.support, c x * (e.repr x k : ℂ)
  have hγ : ∀ v, eigComp ρ s v = ∑ k, γ k • ρ (e k) v := by
    intro v
    rw [hc1]
    simp only [γ, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ρ x = ρ (∑ k, e.repr x k • e k) := by rw [e.sum_repr]
    rw [hx]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, mul_smul,
      Int.cast_smul_eq_zsmul]
  have hk : ∃ k, γ k ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply h0
    rw [← hc3 x₀ hx₀, hγ]
    simp [hn]
  obtain ⟨k₀, hk₀⟩ := hk
  have h1 : LinearIndependent ℤ fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r => e p.1 • y p.2 :=
    linearIndependent_smul e.linearIndependent hli
  have hmem : ∀ p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r, ((e p.1 • y p.2 : W) : Λ) ∈ I :=
    fun p => I.smul_mem _ (hy p.2)
  have h2 : LinearIndependent ℤ fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r =>
      u ((e p.1 • y p.2 : W) : Λ) := by
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro l hl
    refine h1 l (hinj ?_)
    rw [hu _ (by rw [Submodule.coe_sum]; exact I.sum_mem fun p _ => zsmul_mem (hmem p) _), map_zero]
    have : u ((∑ p, l p • e p.1 • y p.2 : W) : Λ) = 0 := by
      rw [← hl, Submodule.coe_sum, map_sum]
      exact Finset.sum_congr rfl fun p _ => map_zsmul u _ _
    rw [this]
    have : cst (0 : Fin g → ℤ) = 0 := by funext k; simp [cst]
    rw [this, mulVec_zero]
  have h3 : LinearIndependent ℂ fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r =>
      cst (u ((e p.1 • y p.2 : W) : Λ)) := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℂ)).2 h2
  have h4 : LinearIndependent ℂ fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r =>
      ρ (e p.1) (per (y p.2)) := by
    have := h3.map' M.mulVecLin (LinearMap.ker_eq_bot.2 (mulVec_injective_of_det_ne_zero hM))
    have e4 : (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r => ρ (e p.1) (per (y p.2))) =
        M.mulVecLin ∘ fun p => cst (u ((e p.1 • y p.2 : W) : Λ)) := by
      funext p
      rw [← hact, hu _ (hmem p)]
      rfl
    rw [e4]
    exact this
  rw [Fintype.linearIndependent_iff] at h4 ⊢
  intro l hl a
  have := h4 (fun p => l p.2 * γ p.1) (by
    rw [← hl, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hγ, Finset.smul_sum, mul_smul]) (k₀, a)
  exact (mul_eq_zero.1 this).resolve_right hk₀

theorem oFamily_image {E : Type} [Field E] [NumberField E] {g r : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {W I : Submodule (𝓞 E) Λ} (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hIW : I ≤ W)
    (hinj : Function.Injective per) (hact : ∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x))
    (y : Fin r → W) (hy : ∀ a, (y a : Λ) ∈ I) (hli : LinearIndependent (𝓞 E) y)
    (hidx : (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0) :
    IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) fun a => per (y a) := by
  classical
  set J : Submodule (𝓞 E) W := I.comap W.subtype with hJ
  have hS : AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} = J.toAddSubgroup.map per := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro p ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro p ⟨x, hx, rfl⟩
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
  have hsum : ∀ c : Fin r → 𝓞 E, per (∑ i, c i • y i) = ∑ i, ρ (c i) (per (y i)) := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hact _ _
  refine ⟨fun a => AddSubgroup.subset_closure ⟨y a, hy a, rfl⟩, fun c hc => ?_, ?_⟩
  · funext i
    exact Fintype.linearIndependent_iff.1 hli c (hinj (by rw [hsum, hc, map_zero])) i
  · set P : Submodule (𝓞 E) W := Submodule.span (𝓞 E) (Set.range y) with hP
    have hspan : oSpan ρ (fun a => per (y a)) = P.toAddSubgroup.map per := by
      apply le_antisymm
      · rw [oSpan, AddSubgroup.closure_le]
        rintro p ⟨a, i, rfl⟩
        exact ⟨a • y i, P.smul_mem a (Submodule.subset_span ⟨i, rfl⟩), hact _ _⟩
      · rintro p ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
        show per _ ∈ _
        rw [hsum]
        exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, rfl⟩
    have hPΛ : (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup
        = P.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      have : Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ)) = P.map W.subtype := by
        rw [hP, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [this]
      ext x
      simp
    have hIΛ : I.toAddSubgroup = J.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hIW hx⟩, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [hPΛ, hIΛ, AddSubgroup.relIndex_map_map_of_injective _ _ W.injective_subtype] at hidx
    rw [hspan, hS, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hidx

theorem exists_phiNormSq {O Ψ : Type} [CommRing O] [Fintype Ψ] {g m r : ℕ} [Nonempty Ψ]
    (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (hb : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (I : AddSubgroup (Fin g → ℂ)) (κ : ℝ)
    (σ : Ψ → (O →+* ℂ)) (b : Ψ → Fin m → Fin g → ℂ) (v : Fin r → Fin g → ℂ) (hv : IsOFamily ρ I v)
    (hbi : ∀ τ, LinearIndependent ℂ (b τ)) (hbs : ∀ τ, Submodule.span ℂ (Set.range (b τ)) = eigSp ρ (σ τ))
    (hmem : ∀ τ a, eigComp ρ (σ τ) (v a) ∈ eigSp ρ (σ τ))
    (hli : ∀ τ, LinearIndependent ℂ fun a => eigComp ρ (σ τ) (v a)) : ∃ ν, PhiNormSq ρ hb I κ σ b ν := by
  classical
  have h1 := fun τ => GlobalTheory.T.exists_extend_linearIndependent_of_span g m r _ (b τ) (hli τ) (hbi τ) fun a => by rw [hbs]; exact hmem τ a
  obtain ⟨k, -, rfl, -⟩ := h1 (Classical.arbitrary Ψ)
  have h2 : ∀ τ, ∃ q : Fin k → Fin g → ℂ, (∀ c, q c ∈ eigSp ρ (σ τ)) ∧
      ∃ T : Matrix (Fin (r + k)) (Fin (r + k)) ℂ,
        (∀ i, Fin.append (fun a => eigComp ρ (σ τ) (v a)) q i = ∑ j, T j i • b τ j) ∧ T.det ≠ 0 := by
    intro τ
    obtain ⟨k', J, hk, hl⟩ := h1 τ
    obtain rfl : k' = k := by omega
    have hq : ∀ c, b τ (J c) ∈ eigSp ρ (σ τ) := fun c => by
      rw [← hbs]; exact Submodule.subset_span ⟨_, rfl⟩
    have hT : ∀ i, ∃ t : Fin (r + k') → ℂ,
        ∑ j, t j • b τ j = Fin.append (fun a => eigComp ρ (σ τ) (v a)) (fun c => b τ (J c)) i := by
      intro i
      rw [← Submodule.mem_span_range_iff_exists_fun, hbs]
      refine Fin.addCases (fun a => ?_) (fun c => ?_) i
      · rw [Fin.append_left]; exact hmem τ a
      · rw [Fin.append_right]; exact hq c
    choose t ht using hT
    refine ⟨_, hq, Matrix.of fun j i => t i j, fun i => (ht i).symm, fun hd => ?_⟩
    obtain ⟨l, hl0, hl1⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    refine hl0 (funext (Fintype.linearIndependent_iff.1 hl l ?_))
    simp only [← ht, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have := congrFun hl1 j
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [show ∑ i, l i * t i j = 0 from by rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _,
      zero_smul]
  choose q hq T hT hd using h2
  exact ⟨_, r, k, rfl, v, q, T, hv, hq, hT, hd, rfl⟩

theorem lower_centre {E : Type} [Field E] [NumberField E] [IsCMField E] {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) {m : ℕ}
    (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (hσ : IsCMFam σ) (hm : 1 ≤ m)
    (hb : IsEigFrames (Metric.ball 0 1) L.B σ b) :
    ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ →
      -C ≤ (L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) + (L.riem w hw).cuspW σ := by
  classical
  have hne : Nonempty Ψ := by
    by_contra hn
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, -⟩ := (hσ.2 (s.comp (algebraMap (𝓞 E) E))).2 fun ⟨τ, _⟩ => hn ⟨τ⟩
    exact hn ⟨τ⟩
  obtain ⟨W, I, per, Hb, M, u, hI, hsat, hinj, hact, hM, hu, hν⟩ := limit_strong E n a g Λ Ψ L σ m b hσ hb
  have hIW : I ≤ W := fun x hx => ((hI x).1 hx).1
  have hiso : ∀ w (hw : w ∈ logCover L.a_le), IsIsoSub (L.riem w hw).form I :=
    fun w hw x hx y hy => ((hI x).1 hx).2 y (hIW hy)
  have hw₀ : (fun k : Fin n => if k.val < a then (-1 : ℂ) else 0) ∈ logCover L.a_le := by
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      simp only [hi, if_true]
      norm_num
    · simp [not_lt.2 hk]
  have hfam : ∃ (r : ℕ) (y : Fin r → Λ), (∀ i, y i ∈ I) ∧ LinearIndependent (𝓞 E) y ∧
      (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 := by
    by_cases h : I = ⊥
    · refine ⟨0, Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, ?_⟩
      rw [h]
      simp
    · obtain ⟨r, y, -, h1⟩ := (GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (L.riem _ hw₀) σ I hσ (hiso _ hw₀) h).1
      exact ⟨r, y, h1⟩
  obtain ⟨r, y, hy, hli, hidx⟩ := hfam
  let y' : Fin r → W := fun i => ⟨y i, hIW (hy i)⟩
  have hli' : LinearIndependent (𝓞 E) y' := LinearIndependent.of_comp W.subtype hli
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ν, hν'⟩ := exists_phiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) _ 1 σ (fun τ i => b τ i 0) _
    (oFamily_image per (L.B 0) hIW hinj hact y' hy hli' hidx) (fun τ => (hb.2 0 h0 τ).1) (fun τ => (hb.2 0 h0 τ).2)
    (fun τ a => ((GlobalTheory.T.exists_eigenComponent_polynomial E (σ τ)).choose_spec _ (L.B 0)).2.1 _)
    fun τ => eig_indep per (L.B 0) M u hinj hact hM hu y' hy hli' (σ τ) (x₀ := b τ ⟨0, hm⟩ 0)
      (by rw [← (hb.2 0 h0 τ).2]; exact Submodule.subset_span ⟨_, rfl⟩) ((hb.2 0 h0 τ).1.ne_zero ⟨0, hm⟩)
  obtain ⟨δ, hδ, h⟩ := (hν ν hν').2 1 one_pos
  refine ⟨min δ 1, lt_min hδ one_pos, 1 - Real.log ν, fun w hw hwδ => ?_⟩
  have h1 := (abs_lt.1 (h w hw (hwδ.trans_le (min_le_left _ _)))).1
  have hz : expCover a w ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    mem_ball_zero_iff.2 (hwδ.trans_le (min_le_right _ _))
  have hrk : (L.riem w hw).HasRank σ m := fun τ => by
    show Module.finrank ℂ (eigSp (L.B (expCover a w)) (σ τ)) = m
    rw [← (hb.2 _ hz τ).2, finrank_span_eq_card (hb.2 _ hz τ).1, Fintype.card_fin]
  obtain ⟨-, -, h2, h3, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (L.riem w hw) σ m hσ hrk hm
  have h4 : -Real.log ((L.riem w hw).nz σ I) ≤ (L.riem w hw).cuspW σ := by
    by_cases hI0 : I = ⊥
    · have : (L.riem w hw).nz σ I = 1 := by
        refine dif_neg ?_
        rintro ⟨r, v, hr, hv, hl, -⟩
        exact hl.ne_zero ⟨0, hr⟩ (by simpa [hI0] using hv ⟨0, hr⟩)
      rw [this, Real.log_one, neg_zero]
      exact h3
    · exact (h2 I ⟨hI0, hsat, hiso w hw⟩).1
  linarith

end LevelTowerAlt
