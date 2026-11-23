import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt

noncomputable section

namespace PositivityTheory.Mix.Real

open SchwartzMap MeasureTheory FourierTransform
open scoped RealInnerProductSpace

def ee (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_temp : ee.HasTemperateGrowth := by
  have hc : Real.cos.HasTemperateGrowth := ⟨Real.contDiff_cos, fun n => ⟨0, 1, fun x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simpa using Real.abs_iteratedDeriv_cos_le_one n x⟩⟩
  have hs : Real.sin.HasTemperateGrowth := ⟨Real.contDiff_sin, fun n => ⟨0, 1, fun x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simpa using Real.abs_iteratedDeriv_sin_le_one n x⟩⟩
  have hl : (fun t : ℝ => -(2 * Real.pi) * t).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul Function.HasTemperateGrowth.id'
  have e : ee = fun t => ((Real.cos (-(2 * Real.pi) * t) : ℝ) : ℂ) + ((Real.sin (-(2 * Real.pi) * t) : ℝ) : ℂ) * Complex.I := by
    funext t
    rw [ee, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    congr 1; push_cast; ring
  rw [e]
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp (hc.comp hl)).add
    ((Complex.ofRealCLM.hasTemperateGrowth.comp (hs.comp hl)).mul (Function.HasTemperateGrowth.const _))

section Gen

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def Tr (β : X → X → ℝ) (w : X × X) (f g : 𝓢(X, ℂ)) : Prop := ∀ x, g x = ee (β x w.2 + β w.1 w.2 / 2) * f (x + w.1)

def cmp (A : X ≃L[ℝ] Y) : 𝓢(X, ℂ) ≃L[ℂ] 𝓢(Y, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (compCLMOfContinuousLinearEquiv ℂ A.symm) (compCLMOfContinuousLinearEquiv ℂ A)
    (fun f => by ext x; simp) (fun f => by ext x; simp)

theorem tr_cmp {β : X → X → ℝ} {β' : Y → Y → ℝ} (A : X ≃L[ℝ] Y) (B : X → Y) (h : ∀ x y, β' (A x) (B y) = β x y) {w : X × X}
    {f g : 𝓢(X, ℂ)} (H : Tr β w f g) : Tr β' (A w.1, B w.2) (cmp A f) (cmp A g) := fun y => by
  obtain ⟨x, rfl⟩ := A.surjective y
  change g (A.symm (A x)) = _ * f (A.symm (A x + A w.1))
  rw [← map_add, A.symm_apply_apply, A.symm_apply_apply, H x, h, h]

end Gen

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def Impl (S : V × V → V × V) : Prop :=
  ∃ T : 𝓢(V, ℂ) ≃L[ℂ] 𝓢(V, ℂ), ∀ w f g, Tr (inner ℝ) w f g → Tr (inner ℝ) (S w) (T f) (T g)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem Impl.comp {S S' : V × V → V × V} (h : Impl S) (h' : Impl S') : Impl fun w => S (S' w) :=
  let ⟨T, hT⟩ := h
  let ⟨T', hT'⟩ := h'
  ⟨T'.trans T, fun w f g H => hT _ _ _ (hT' w f g H)⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem implM (A : V ≃L[ℝ] V) (B : V → V) (h : ∀ x y, ⟪A x, B y⟫ = ⟪x, y⟫) : Impl fun w : V × V => (A w.1, B w.2) :=
  ⟨cmp A, fun _ _ _ H => tr_cmp A B h H⟩

omit [MeasurableSpace V] [BorelSpace V] in
theorem implN (Q : V →ₗ[ℝ] V) (h : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫) : Impl fun w : V × V => (w.1, w.2 + Q w.1) := by
  have hq : ∀ c : ℝ, (fun x : V => ee (c * ⟪x, Q x⟫)).HasTemperateGrowth := fun c =>
    ee_temp.comp ((Function.HasTemperateGrowth.const c).mul ((innerSL ℝ).bilinear_hasTemperateGrowth
      Function.HasTemperateGrowth.id' (LinearMap.toContinuousLinearMap Q).hasTemperateGrowth))
  have hi : ∀ c : ℝ, ∀ f : 𝓢(V, ℂ), smulLeftCLM ℂ (fun x : V => ee (-c * ⟪x, Q x⟫))
      (smulLeftCLM ℂ (fun x : V => ee (c * ⟪x, Q x⟫)) f) = f := fun c f => by
    ext x
    rw [smulLeftCLM_apply_apply (hq _), smulLeftCLM_apply_apply (hq _), smul_smul, ← ee_add]
    simp [ee_zero]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (smulLeftCLM ℂ fun x : V => ee (-(1 / 2) * ⟪x, Q x⟫))
    (smulLeftCLM ℂ fun x : V => ee (- -(1 / 2) * ⟪x, Q x⟫)) (hi _) (fun f => by simpa using hi (1 / 2) f), fun w f g H x => ?_⟩
  simp only [ContinuousLinearEquiv.equivOfInverse_apply, smulLeftCLM_apply_apply (hq _), smul_eq_mul]
  rw [H x, ← mul_assoc, ← mul_assoc, ← ee_add, ← ee_add]
  congr 2
  simp only [map_add, inner_add_left, inner_add_right, h w.1 x]
  ring

theorem implJ : Impl fun w : V × V => (w.2, -w.1) := by
  refine ⟨fourierCLE ℂ 𝓢(V, ℂ), fun w f g H ξ => ?_⟩
  have e : ∀ (φ : 𝓢(V, ℂ)) (η : V), fourierCLE ℂ 𝓢(V, ℂ) φ η = ∫ v, ee ⟪v, η⟫ * φ v := fun φ η => by
    rw [fourierCLE_apply, fourier_coe, Real.fourier_eq']
    congr 1; funext v
    rw [smul_eq_mul, ee]; congr 2; push_cast; ring
  rw [e, e, ← integral_const_mul, ← integral_add_right_eq_self (fun v => _ * (ee ⟪v, ξ + w.2⟫ * f v)) w.1]
  congr 1; funext v
  rw [H v, ← mul_assoc, ← mul_assoc, ← ee_add, ← ee_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_right, real_inner_comm w.1 ξ, real_inner_comm w.1 w.2]
  ring

theorem implJ' : Impl fun w : V × V => (-w.2, w.1) := by
  simpa using implJ.comp (implM (ContinuousLinearEquiv.neg ℝ (M := V)) (fun y => -y) fun x y => by simp)

theorem implU (Q : V →ₗ[ℝ] V) (h : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫) : Impl fun w : V × V => (w.1 + Q w.2, w.2) := by
  have := implJ'.comp ((implN (-Q) fun x y => by simp [inner_neg_right, h x y]).comp implJ)
  simpa [add_comm] using this

def Sp (S : V × V →ₗ[ℝ] V × V) : Prop := ∀ w w', ⟪(S w).1, (S w').2⟫ - ⟪(S w').1, (S w).2⟫ = ⟪w.1, w'.2⟫ - ⟪w'.1, w.2⟫

omit [MeasurableSpace V] [BorelSpace V] in
theorem implP (R : V × V →ₗ[ℝ] V × V) (hR : Sp R) (h0 : ∀ y, (R (0, y)).1 = 0) : Impl R := by
  let a : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ R ∘ₗ LinearMap.inl ℝ V V
  let c : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ R ∘ₗ LinearMap.inl ℝ V V
  have h1 : ∀ x y, ⟪a x, (R (0, y)).2⟫ = ⟪x, y⟫ := fun x y => by simpa [h0, a] using hR (x, 0) (0, y)
  have hi : Function.Injective a := (injective_iff_map_eq_zero a).2 fun x hx => by
    have := h1 x x
    rw [hx, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  let A := (LinearEquiv.ofInjectiveEndo a hi).toContinuousLinearEquiv
  have hA : ∀ x, A x = a x := fun _ => rfl
  have := (implN (c ∘ₗ (A.symm : V →L[ℝ] V).toLinearMap) fun x y => by
    obtain ⟨x, rfl⟩ := A.surjective x
    obtain ⟨y, rfl⟩ := A.surjective y
    have := hR (x, 0) (y, 0)
    simp only [inner_zero_right, sub_self, sub_eq_zero] at this
    have key : ⟪A x, c y⟫ = ⟪A y, c x⟫ := this
    simpa using key).comp (implM A (fun y => (R (0, y)).2) h1)
  convert this using 1
  funext w
  have e : R w = R (w.1, 0) + R (0, w.2) := by rw [← map_add]; simp
  refine Prod.ext ?_ ?_
  · rw [e, Prod.fst_add, h0, add_zero]; rfl
  · rw [e, Prod.snd_add, add_comm]; simp [c]

theorem implSp (S : V × V →ₗ[ℝ] V × V) (hS : Sp S) : Impl S := by
  let b : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ S ∘ₗ LinearMap.inr ℝ V V
  let d : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ S ∘ₗ LinearMap.inr ℝ V V
  have hbd : ∀ y z, ⟪b y, d z⟫ = ⟪b z, d y⟫ := fun y z => by
    have := hS (0, y) (0, z)
    simp only [inner_zero_left, sub_self, sub_eq_zero] at this
    exact this
  let P : V →ₗ[ℝ] V := ((LinearMap.range b)ᗮ.starProjection : V →L[ℝ] V).toLinearMap
  have hP : ∀ x y, ⟪x, P y⟫ = ⟪y, P x⟫ := fun x y => by
    change ⟪x, (LinearMap.range b)ᗮ.starProjection y⟫ = ⟪y, (LinearMap.range b)ᗮ.starProjection x⟫
    rw [← Submodule.inner_starProjection_left_eq_right, real_inner_comm]
  have hi : Function.Injective (b + P ∘ₗ d) := (injective_iff_map_eq_zero _).2 fun y hy => by
    have hy' : b y + P (d y) = 0 := hy
    have hm : P (d y) ∈ (LinearMap.range b)ᗮ := Submodule.starProjection_apply_mem _ _
    have hb : b y = 0 := by
      have := Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self b y) hm
      rw [eq_neg_of_add_eq_zero_right hy', inner_neg_right, neg_eq_zero] at this
      exact inner_self_eq_zero.1 this
    have hd : d y ∈ (LinearMap.range b)ᗮ := (Submodule.mem_orthogonal _ _).2 (by
      rintro _ ⟨z, rfl⟩
      rw [hbd, hb, inner_zero_left])
    have hd0 : d y = 0 := by
      rw [hb, zero_add] at hy'
      exact (Submodule.starProjection_eq_self_iff.2 hd).symm.trans hy'
    have := hS (y, 0) (0, y)
    change ⟪_, d y⟫ - ⟪b y, _⟫ = _ at this
    rw [hb, hd0, inner_zero_left, inner_zero_right, sub_self] at this
    simpa using this.symm
  let B := LinearEquiv.ofInjectiveEndo _ hi
  have hB : ∀ y, B y = b y + P (d y) := fun _ => rfl
  let Q : V →ₗ[ℝ] V := d ∘ₗ B.symm.toLinearMap
  have hQ : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫ := fun x y => by
    obtain ⟨x, rfl⟩ := B.surjective x
    obtain ⟨y, rfl⟩ := B.surjective y
    simp only [Q, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hB, hB, inner_add_left, inner_add_left, hbd, real_inner_comm (d y), real_inner_comm (d x) (P _), hP]
  let u : V × V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ S + P ∘ₗ LinearMap.snd ℝ V V ∘ₗ S
  let R : V × V →ₗ[ℝ] V × V := (LinearMap.snd ℝ V V ∘ₗ S - Q ∘ₗ u).prod (-u)
  have hR : ∀ w, R w = ((S w).2 - Q ((S w).1 + P (S w).2), -((S w).1 + P (S w).2)) := fun _ => rfl
  have hsp : Sp R := fun w w' => by
    rw [← hS w w', hR, hR]
    have e1 := hQ ((S w).1 + P (S w).2) ((S w').1 + P (S w').2)
    have e2 := hP (S w).2 (S w').2
    simp only [inner_neg_right, inner_sub_left, real_inner_comm _ (Q _)]
    simp only [inner_add_right (S w).2, inner_add_right (S w').2, real_inner_comm (S w).1, real_inner_comm (S w').1] at *
    linarith
  have h0 : ∀ y, (R (0, y)).1 = 0 := fun y => by
    change d y - Q (B y) = 0
    simp [Q]
  have := (implU (-P) fun x y => by simp [inner_neg_right, hP x y]).comp ((implN Q hQ).comp (implJ'.comp (implP R hsp h0)))
  convert this using 1
  funext w
  simp [hR]

end PositivityTheory.Mix.Real

namespace PositivityTheory.Mix

open PositivityTheory.Mix.Real
open scoped RealInnerProductSpace

theorem real_estimates_holds : RealSt := by
  intro X _ _ _ β hs hn S hS
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ X))
  let L : X ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V])
  let l : X →ₗ[ℝ] V := (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
      (β.compl₂ (L.symm : V →L[ℝ] X).toLinearMap)
  have hl : ∀ x y, ⟪L x, l y⟫ = β x y := fun x y => by
    rw [real_inner_comm]
    simp [l, hs x y]
  have hi : Function.Injective l := (injective_iff_map_eq_zero l).2 fun y hy => hn y fun x => by
    rw [hs, ← hl, hy, inner_zero_right]
  let M : X ≃ₗ[ℝ] V := LinearMap.linearEquivOfInjective l hi (by simp [V])
  have hM : ∀ x y, ⟪L x, M y⟫ = β x y := hl
  have hM' : ∀ x y, β (L.symm x) (M.symm y) = ⟪x, y⟫ := fun x y => by rw [← hM]; simp
  let E : (X × X) ≃ₗ[ℝ] (V × V) := L.toLinearEquiv.prodCongr M
  obtain ⟨T, hT⟩ := implSp (E.toLinearMap ∘ₗ S.toLinearMap ∘ₗ E.symm.toLinearMap) fun w w' => by
    change ⟪L _, M _⟫ - ⟪L _, M _⟫ = _
    rw [hM, hM, ← hM', ← hM']
    exact hS _ _
  refine ⟨((cmp L).trans T).trans (cmp L.symm), fun w f g H => ?_⟩
  have h1 := tr_cmp (β' := fun x y => β x y) L.symm M.symm hM'
    (hT _ _ _ (tr_cmp (β := fun x y => β x y) (β' := inner ℝ) L M hM (w := w) H))
  have e : E.symm (L w.1, M w.2) = w := E.symm_apply_apply w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e] at h1
  have e1 : L.symm (E (S w)).1 = (S w).1 := L.symm_apply_apply _
  have e2 : M.symm (E (S w)).2 = (S w).2 := M.symm_apply_apply _
  rw [e1, e2] at h1
  exact h1

end PositivityTheory.Mix
