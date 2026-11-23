import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefDTensActPow

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem coefE_Am_mul (dual : Bool) (g h : Matrix (Fin n) (Fin n) ℂ) :
    coefAm dual (g * h) = coefAm dual g * coefAm dual h := by
  cases dual <;> simp [coefAm, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem coefE_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) (w : Fin n → H) :
    coefTG dual σ (g * h) w = coefTG dual σ g (coefTG dual σ h w) := by
  ext c
  simp only [coefTG, coefE_Am_mul, hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem coefE_tensGrp_one (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (w : Fin n → H) :
    coefTG dual σ 1 w = w := by
  ext c
  cases dual <;> simp [coefTG, coefAm, hσ.1.1, Matrix.one_apply]

def coefLam (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : (Fin n → H) →L[ℂ] ℂ :=
  ∑ c, (innerSL ℂ (f c)).comp (∑ d, coefAm dual g c d • (σ g).comp (ContinuousLinearMap.proj d))

theorem coefLam_apply (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f u : Fin n → H) :
    coefLam dual σ g f u = ∑ c, inner ℂ (f c) (coefTG dual σ g u c) := by
  simp [coefLam, coefTG, inner_sum, inner_smul_right]

def CoefGood (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (X : Matrix (Fin n) (Fin n) ℂ)
    (r₀ : ℝ) : Prop :=
  ∀ v ∈ genSub E V, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧
    ∀ s : ℝ, |s| < r₀ → Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)

theorem coefE_goodP (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    CoefGood E V X (1 / (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) + 1)) := by
  intro v hv
  obtain ⟨a, ha, -, hs⟩ := exists_orbit_bound hσ hD hVf hVK hc hX hv
  refine ⟨a, ha, fun s hs' => hs |s| (abs_nonneg s) ?_⟩
  have hA : 0 ≤ √2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) := by positivity
  rw [lt_div_iff₀ (by positivity)] at hs'
  nlinarith [abs_nonneg s]

theorem coefE_goodK (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (r₀ : ℝ) : CoefGood E V Z r₀ := by
  intro v hv
  obtain ⟨k, hk⟩ := exists_layer_of_mem_genSub hD.glRep hVK hv
  obtain ⟨C, -, hC⟩ := exists_norm_actM_pow_le_of_inK hD.glRep hVK hVf hZ k
  refine ⟨fun m => C ^ m * ‖v‖, fun m => hC v hk m, fun s _ => ?_⟩
  have := (Real.summable_pow_div_factorial (C * |s|)).mul_left ‖v‖
  exact this.congr fun m => by rw [mul_pow]; ring

theorem coefE_ι_act (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) {v : D} (hv : v ∈ genSub E V') :
    ι (actM E X v) = actM (tensF dual E) X (ι v) := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    hιE _ _ v hv]

private theorem actM_pow_apply_mem_genSub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : M} (hv : v ∈ genSub E S) : ((actM E X) ^ m) v ∈ genSub E S := by
  have hE : ∀ a b, ∀ w ∈ genSub E S, E a b w ∈ genSub E S := by
    intro a b w hw
    simp only [genSub, Submodule.mem_sInf, Set.mem_setOf_eq] at hw ⊢
    intro T hT
    exact hT.2 a b w (hw T hT)
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (hE a b _ ih)

theorem coefE_ι_pow (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) {y : D} (hy : y ∈ genSub E V') :
    ι (((actM E X) ^ m) y) = ((actM (tensF dual E) X) ^ m) (ι y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    have h1 : actM E X y ∈ genSub E V' := by simpa using actM_pow_apply_mem_genSub X 1 hy
    rw [pow_succ, Module.End.mul_apply, ih h1,
      coefE_ι_act dual hιE X hy, pow_succ, Module.End.mul_apply]

end Rep

section Propag

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def CoefQ (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ D)
    (V' : Submodule ℂ D) (ι : D →ₗ[ℂ] (Fin n → D)) (f : Fin n → D) (z : D)
    (h : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ y ∈ genSub E V', ∑ c, inner ℂ ((f c : D) : H) (coefTG dual σ h (fun d => ((ι y d : D) : H)) c) =
    inner ℂ ((z : D) : H) (σ h ((y : D) : H))

theorem coefE_one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  simp [UJset, inUJ]

theorem coefE_step (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {r₀ : ℝ}
    (hg : CoefGood E V X r₀) (hg' : CoefGood E V' X r₀) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε)
    (hQ : CoefQ dual σ E V' ι f z h) {s : ℝ} (hs : |s| < r₀) :
    CoefQ dual σ E V' ι f z (h * NormedSpace.exp ((s : ℂ) • X)) := by
  intro y hy
  have he : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε := rq_exp_mem ε X hX s

  have hL : HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
      coefLam dual σ h (fun c => ((f c : D) : H))
        (fun c => ((((actM (tensF dual E) X) ^ m) (ι y) c : D) : H)))
      (coefLam dual σ h (fun c => ((f c : D) : H))
        (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((ι y d : D) : H)))) := by
    apply coefD_taylor dual hσ hD hX
    intro d
    have hyd : ι y d ∈ genSub E V := by
      have := hι1 y hy
      simp only [tensSub, Submodule.mem_pi] at this
      exact this d (Set.mem_univ d)
    obtain ⟨a, ha, hsum⟩ := hg _ hyd
    exact ⟨a, ha, hsum s hs⟩

  obtain ⟨a', ha', hsum'⟩ := hg' y hy
  have hR0 := hasSum_orbit_of_bound hσ hD hX y a' ha' 0 s (by simpa using hsum' s hs)
  have h1 : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    simp [NormedSpace.exp_zero, hσ.1.1]
  simp only [h1, ContinuousLinearMap.one_apply] at hR0
  have hR := ((innerSL ℂ ((z : D) : H)).comp (σ h)).hasSum hR0
  have hterms : (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
      coefLam dual σ h (fun c => ((f c : D) : H))
        (fun c => ((((actM (tensF dual E) X) ^ m) (ι y) c : D) : H))) =
      fun m : ℕ => ((innerSL ℂ ((z : D) : H)).comp (σ h))
        ((((s - 0) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) • ((((actM E X) ^ m) y : D) : H)) := by
    funext m
    rw [← coefE_ι_pow dual hιE X m hy, coefLam_apply,
      hQ _ (actM_pow_apply_mem_genSub X m hy)]
    simp [inner_smul_right]
  rw [hterms] at hL
  have key := hL.unique hR
  rw [coefLam_apply, ← coefE_tensGrp_mul dual hσ hh he] at key
  rw [hσ.1.2 h hh _ he]
  simpa using key

theorem coefE_line (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hg : CoefGood E V X r₀) (hg' : CoefGood E V' X r₀) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε)
    (hQ : CoefQ dual σ E V' ι f z h) (t : ℝ) :
    CoefQ dual σ E V' ι f z (h * NormedSpace.exp ((t : ℂ) • X)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / r₀)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hr₀.le) hN
  have hs : |t / N| < r₀ := by
    rw [abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hr₀] at hN
    linarith
  have key : ∀ k : ℕ, h * NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X) ∈ UJset ε ∧
      CoefQ dual σ E V' ι f z (h * NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X)) := by
    intro k
    induction k with
    | zero => simpa [NormedSpace.exp_zero] using ⟨hh, hQ⟩
    | succ k ih =>
      have hexp : NormedSpace.exp (((((k + 1 : ℕ) : ℝ) * (t / N) : ℝ) : ℂ) • X) =
          NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X) * NormedSpace.exp (((t / N : ℝ) : ℂ) • X) := by
        rw [← Matrix.exp_add_of_commute]
        · congr 1
          push_cast
          rw [← add_smul]
          congr 1
          ring
        · exact ((Commute.refl X).smul_left _).smul_right _
      rw [hexp, ← mul_assoc]
      exact ⟨rq_UJ_mul ih.1 (rq_exp_mem ε X hX _),
        coefE_step dual hσ hD hX hg hg' hι1 hιE f z ih.1 ih.2 hs⟩
  have := (key N).2
  rwa [show ((N : ℝ) * (t / N)) = t by field_simp] at this

theorem coefE_all (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'K : IsKStableSub ε E V') {c' : ℝ} (hc' : ∀ v ∈ V', casimir E v = (c' : ℂ) • v)
    {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D)
    (hz : ∀ y ∈ genSub E V', inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c)) :
    ∀ g ∈ UJset ε, CoefQ dual σ E V' ι f z g := by
  intro g hg
  obtain ⟨k, hk, Y, hY, rfl⟩ := polar_UJ hg
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk

  have hQ1 : CoefQ dual σ E V' ι f z 1 := by
    intro y hy
    rw [coefE_tensGrp_one dual hσ, hσ.1.1, ContinuousLinearMap.one_apply]
    simp only [← Submodule.coe_inner]
    exact (hz y hy).symm

  have hZ1 := coefE_line dual hσ hD hZ.1 one_pos (coefE_goodK hD hVf hVK hZ 1)
    (coefE_goodK hD hV'f hV'K hZ 1) hι1 hιE f z coefE_one_mem hQ1 1
  simp only [one_mul, Complex.ofReal_one, one_smul] at hZ1

  have hr : 0 < 1 / (√2 * √(∑ a, ∑ b, ‖Y a b‖ ^ 2) + 1) := by positivity
  have hY1 := coefE_line dual hσ hD hY.1 hr (coefE_goodP hσ hD hVf hVK hc hY)
    (coefE_goodP hσ hD hV'f hV'K hc' hY) hι1 hιE f z (rq_K_UJ hk) hZ1 1
  simpa using hY1

end Propag

end ReciprocityTheory.ChartRestriction.DS
