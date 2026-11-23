import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

noncomputable section

open MeasureTheory PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section Haar

variable {n : ℕ} [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure]

private theorem eq_of_univ (μ : Measure (Un n)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (h : μ Set.univ = ν Set.univ) : μ = ν := by
  obtain ⟨c, e⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isMulInvariant_eq_smul_of_compactSpace μ ν⟩
  have h0 : ν Set.univ ≠ 0 := (Measure.measure_univ_pos.2 (NeZero.ne ν)).ne'
  have hT : ν Set.univ ≠ ⊤ := measure_ne_top ν _
  have h1 : ν Set.univ = (c : ENNReal) * ν Set.univ := by
    rw [← h]
    conv_lhs => rw [e]
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hc : (c : ENNReal) = 1 := (ENNReal.mul_left_inj h0 hT).1 (by simpa using h1.symm)
  have hc' : c = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

private theorem rightInv : ν.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : (Measure.map (· * g) ν).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) (measurable_mul_const g)]
    have : ((h * ·) ∘ (· * g) : Un n → Un n) = (· * g) ∘ (h * ·) := by
      funext x
      simp [mul_assoc]
    rw [this, ← Measure.map_map (measurable_mul_const g) (measurable_const_mul h),
      map_mul_left_eq_self]
  refine eq_of_univ ν _ ?_
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
  simp

private theorem invInv : ν.IsInvInvariant := by
  haveI := rightInv ν
  refine ⟨eq_of_univ ν _ ?_⟩
  simp [Measure.inv_apply]

end Haar

section Abs

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private def IsWk [MeasurableSpace (Un n)] (ν : Measure (Un n)) (σ : Un n →* (V →ₗ[ℂ] V)) (c : Un n → ℂ) (v p : V) : Prop :=
  ∀ w : V, ⟪w, p⟫_ℂ = ∫ κ, c κ * ⟪w, σ κ v⟫_ℂ ∂ν

private theorem moveσ {σ : Un n →* (V →ₗ[ℂ] V)} (hσ : IsK σ) (g : Un n) (w x : V) :
    ⟪w, σ g x⟫_ℂ = ⟪σ g⁻¹ w, x⟫_ℂ := by
  have h : σ g (σ g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← hσ.iso g (σ g⁻¹ w) x, h]

variable [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [IsFiniteMeasure ν]
  {σ : Un n →* (V →ₗ[ℂ] V)}

private theorem intg (hσ : IsK σ) {c : Un n → ℂ} (hc : Continuous c) (v w : V) :
    Integrable (fun κ => c κ * ⟪w, σ κ v⟫_ℂ) ν :=
  (hc.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exists_in (hσ : IsK σ) {c : Un n → ℂ} (hc : Continuous c) {v : V} (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (hv : v ∈ S) (hS : ∀ k, ∀ w ∈ S, σ k w ∈ S) :
    ∃ p ∈ S, IsWk ν σ c v p := by
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  let G : Un n → S := fun κ => ⟨σ κ v, hS κ v hv⟩
  let b := stdOrthonormalBasis ℂ S
  have hG : Continuous G := by
    have e : G = fun κ => ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • b i := by
      funext κ
      have := b.sum_repr' (G κ)
      simpa [G, Submodule.coe_inner] using this.symm
    rw [e]
    exact continuous_finset_sum _ fun i _ => (hσ.cont v _).smul continuous_const
  have hF : Integrable (fun κ => c κ • G κ) ν :=
    (hc.smul hG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨((∫ κ, c κ • G κ ∂ν : S) : V), Subtype.coe_prop _, fun w => ?_⟩
  let L : S →L[ℂ] ℂ := (innerSL ℂ w).comp S.subtypeL
  have := L.integral_comp_comm hF
  have e : ∀ y : S, L y = ⟪w, (y : V)⟫_ℂ := fun y => rfl
  rw [← e, ← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp [e, G, inner_smul_right]

private theorem wk_unique {c : Un n → ℂ} {v p q : V} (hp : IsWk ν σ c v p) (hq : IsWk ν σ c v q) : p = q :=
  ext_inner_left ℂ fun w => by rw [hp w, hq w]

private theorem exists_op (hσ : IsK σ) {c : Un n → ℂ} (hc : Continuous c) :
    ∃ P : Module.End ℂ V, ∀ v, IsWk ν σ c v (P v) := by
  have h : ∀ v : V, ∃ p, IsWk ν σ c v p := fun v => by
    obtain ⟨S, hfd, hv, hS⟩ := hσ.fin v
    obtain ⟨p, -, hp⟩ := exists_in ν hσ hc S hv hS
    exact ⟨p, hp⟩
  choose p hp using h
  refine ⟨{ toFun := p, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hp⟩
  · refine ext_inner_left ℂ fun w => ?_
    rw [inner_add_right, hp, hp, hp, ← integral_add (intg ν hσ hc x w) (intg ν hσ hc y w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_add, inner_add_right, mul_add]
  · refine ext_inner_left ℂ fun w => ?_
    rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_smul, inner_smul_right]
    ring

private theorem comm_adj {c : Un n → ℂ} {P B : Module.End ℂ V} (hP : ∀ v, IsWk ν σ c v (P v))
    (hB : AdjComm σ B) : P * B = B * P := by
  obtain ⟨B', hadj, hcomm⟩ := hB
  have key : ∀ x y : V, ⟪x, B y⟫_ℂ = ⟪B' x, y⟫_ℂ := fun x y => by
    rw [← inner_conj_symm, hadj, inner_conj_symm]
  refine LinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  simp only [Module.End.mul_apply]
  rw [hP (B v) w, key, hP v (B' w)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  have h := LinearMap.congr_fun (hcomm κ).1 v
  simp only [Module.End.mul_apply] at h
  simp only []
  rw [← h, key]

private theorem mem_stable (hσ : IsK σ) {c : Un n → ℂ} (hc : Continuous c) {P : Module.End ℂ V}
    (hP : ∀ v, IsWk ν σ c v (P v)) (N : Submodule ℂ V) (hN : ∀ k, ∀ x ∈ N, σ k x ∈ N) {x : V} (hx : x ∈ N) :
    P x ∈ N := by
  obtain ⟨S, hfd, hv, hS⟩ := hσ.fin x
  haveI : FiniteDimensional ℂ ↥(S ⊓ N) := Submodule.finiteDimensional_inf_left S N
  obtain ⟨p, hp, hw⟩ := exists_in ν hσ hc (S ⊓ N) ⟨hv, hx⟩ fun k w hw => ⟨hS k w hw.1, hN k w hw.2⟩
  rw [wk_unique ν (hP x) hw]
  exact hp.2

private theorem comm_σ [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (hσ : IsK σ) {c : Un n → ℂ}
    (hcl : ∀ g κ, c (g * κ * g⁻¹) = c κ) {P : Module.End ℂ V} (hP : ∀ v, IsWk ν σ c v (P v)) (g : Un n) :
    P * σ g = σ g * P := by
  refine LinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  simp only [Module.End.mul_apply]
  rw [hP (σ g v) w, moveσ hσ, hP v (σ g⁻¹ w),
    ← integral_mul_left_eq_self (fun κ => c κ * ⟪w, σ κ (σ g v)⟫_ℂ) g,
    ← integral_mul_right_eq_self (fun κ => c (g * κ) * ⟪w, σ (g * κ) (σ g v)⟫_ℂ) g⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only []
  have h : σ (g * κ * g⁻¹) (σ g v) = σ g (σ κ v) := by
    have e : g * κ * g⁻¹ * g = g * κ := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  rw [← mul_assoc, hcl, h, moveσ hσ g w]

private theorem adj_avg [ν.IsInvInvariant] (hσ : IsK σ) {c : Un n → ℂ} {P P' : Module.End ℂ V}
    (hP : ∀ v, IsWk ν σ c v (P v)) (hP' : ∀ v, IsWk ν σ (fun κ => conj (c κ⁻¹)) v (P' v)) (x y : V) :
    ⟪P x, y⟫_ℂ = ⟪x, P' y⟫_ℂ := by
  rw [← inner_conj_symm, hP x y, hP' y x, ← integral_conj,
    ← integral_inv_eq_self (fun κ => conj (c κ⁻¹) * ⟪x, σ κ y⟫_ℂ) ν]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [map_mul, inner_conj_symm, inv_inv]
  rw [moveσ hσ κ⁻¹ x y, inv_inv]

private theorem exists_map [ν.IsMulLeftInvariant] (hσ : IsK σ) (E : KMod n) (e : E.V) (x : V) :
    ∃ t ∈ invA σ E, ∀ ξ : E.V →L[ℂ] ℂ, IsWk ν σ (fun κ => ξ (E.ρ κ e)) x (t ξ) := by
  have hc : ∀ ξ : E.V →L[ℂ] ℂ, Continuous fun κ : Un n => ξ (E.ρ κ e) := fun ξ =>
    ξ.continuous.comp ((ContinuousLinearMap.apply ℂ E.V e).continuous.comp E.cont)
  have h : ∀ ξ : E.V →L[ℂ] ℂ, ∃ p, IsWk ν σ (fun κ => ξ (E.ρ κ e)) x p := fun ξ => by
    obtain ⟨S, hfd, hv, hS⟩ := hσ.fin x
    obtain ⟨p, -, hp⟩ := exists_in ν hσ (hc ξ) S hv hS
    exact ⟨p, hp⟩
  choose p hp using h
  let t : (E.V →L[ℂ] ℂ) →ₗ[ℂ] V :=
    { toFun := p
      map_add' := fun a b => by
        refine ext_inner_left ℂ fun w => ?_
        rw [inner_add_right, hp, hp, hp, ← integral_add (intg ν hσ (hc a) x w) (intg ν hσ (hc b) x w)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
        simp only [ContinuousLinearMap.add_apply, add_mul]
      map_smul' := fun a b => by
        refine ext_inner_left ℂ fun w => ?_
        rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc] }
  refine ⟨t, fun k ξ => ext_inner_left ℂ fun w => ?_, hp⟩
  show ⟪w, p _⟫_ℂ = ⟪w, σ k (p ξ)⟫_ℂ
  rw [moveσ hσ, hp, hp, ← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  have e1 : E.ρ k⁻¹ (E.ρ (k * κ) e) = E.ρ κ e := by
    rw [map_mul, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, ContinuousLinearMap.one_apply]
  have e2 : σ (k * κ) x = σ k (σ κ x) := by rw [map_mul, Module.End.mul_apply]
  simp only [ContinuousLinearMap.comp_apply, e1, e2]
  rw [moveσ hσ k w]

private theorem tr_eq (E : KMod n) (T : E.V →L[ℂ] E.V) (κ : Un n) :
    LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∑ i, innerSL ℂ (stdOrthonormalBasis ℂ E.V i) (E.ρ κ (T (stdOrthonormalBasis ℂ E.V i))) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E.V)]
  rfl

private theorem mem_iso [ν.IsMulLeftInvariant] (hσ : IsK σ) (E : KMod n) (T : E.V →L[ℂ] E.V) {P : Module.End ℂ V}
    (hP : ∀ v, IsWk ν σ (fun κ => LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)) v (P v)) (x : V) :
    P x ∈ isoSp σ E := by
  let b := stdOrthonormalBasis ℂ E.V
  choose t ht hw using fun i => exists_map ν hσ E (T (b i)) x
  have hsum : P x = ∑ i, t i (innerSL ℂ (b i)) := by
    refine ext_inner_left ℂ fun w => ?_
    rw [hP x w, inner_sum]
    simp_rw [fun i => hw i (innerSL ℂ (b i)) w]
    rw [← integral_finset_sum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
      simp only []
      rw [tr_eq, Finset.sum_mul]
    · intro i _
      exact intg ν hσ ((innerSL ℂ (b i)).continuous.comp
        ((ContinuousLinearMap.apply ℂ E.V (T (b i))).continuous.comp E.cont)) x w
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact (le_iSup (fun s : invA σ E => LinearMap.range s.1) ⟨t i, ht i⟩) ⟨_, rfl⟩

private theorem tr_class (E : KMod n) {T : E.V →L[ℂ] E.V} (hT : ∀ k, T * E.ρ k = E.ρ k * T) (g κ : Un n) :
    LinearMap.trace ℂ E.V ((E.ρ (g * κ * g⁻¹) * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  have e : (E.ρ (g * κ * g⁻¹) * T : E.V →L[ℂ] E.V) = E.ρ g * (E.ρ κ * T) * E.ρ g⁻¹ := by
    rw [map_mul, map_mul, mul_assoc _ _ T, ← hT g⁻¹]
    simp only [mul_assoc]
  have e1 : ((E.ρ g⁻¹ : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) * ((E.ρ g : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) = 1 := by
    refine LinearMap.ext fun x => ?_
    show (E.ρ g⁻¹ * E.ρ g) x = x
    rw [← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [e]
  show LinearMap.trace ℂ E.V (((E.ρ g : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) * ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) *
    ((E.ρ g⁻¹ : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)) = _
  rw [LinearMap.trace_mul_comm, ← mul_assoc, e1, one_mul]

end Abs

theorem avgFacts : AvgFacts := by
  intro n _ _ ν _ V _ _ σ hσ E T P hT hP
  haveI := rightInv ν
  haveI := invInv ν
  set c : Un n → ℂ := fun κ => LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) with hcdef
  have hc : Continuous c := by
    let L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)
    exact L.continuous_of_finiteDimensional.comp (E.cont.mul continuous_const)
  have hcl : ∀ g κ, c (g * κ * g⁻¹) = c κ := tr_class E hT
  have hw : ∀ v, IsWk ν σ c v (P v) := fun v w => hP v w
  have hc' : Continuous fun κ : Un n => conj (c κ⁻¹) :=
    Complex.continuous_conj.comp (hc.comp continuous_inv)
  have hcl' : ∀ g κ, conj (c (g * κ * g⁻¹)⁻¹) = conj (c κ⁻¹) := fun g κ => by
    have e : (g * κ * g⁻¹)⁻¹ = g * κ⁻¹ * g⁻¹ := by group
    rw [e, hcl]
  obtain ⟨P', hw'⟩ := exists_op ν hσ hc'
  have hadj := adj_avg ν hσ hw hw'
  refine ⟨mem_iso ν hσ E T hw, ⟨P', hadj, fun k => ⟨comm_σ ν hσ hcl hw k, comm_σ ν hσ hcl' hw' k⟩⟩,
    fun B hB => comm_adj ν hw hB, fun N hN x hx => mem_stable ν hσ hc hw N hN hx, P', hadj,
    fun B hB => comm_adj ν hw' hB⟩

end UpperTheory.V.Z.GSp4Splitting
