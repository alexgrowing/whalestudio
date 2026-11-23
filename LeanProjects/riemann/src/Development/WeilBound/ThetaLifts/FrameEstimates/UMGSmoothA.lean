import Mathlib

noncomputable section

namespace PositivityTheory.ThKEst.UMGS

open Filter Topology Function

theorem hasFDerivAt_of_partials {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by
  induction k with
  | zero =>
    intro Φ D _ _ t
    simpa using hasFDerivAt_of_subsingleton (𝕜 := ℝ) Φ t
  | succ k ih =>
    intro Φ D hc hd t
    have hcons : Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp continuous_snd
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t 0, Fin.tail t))
      (f := fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u))
      (f₁ := fun s u => (ContinuousLinearMap.id ℝ ℝ).smulRight (D 0 (Fin.cons s u)))
      (f₂ := fun s u => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i.succ (Fin.cons s u)))
      (Eventually.of_forall fun v => by
        have h := hd 0 (Fin.cons v.1 v.2)
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h
        have h0 : HasDerivAt (fun s => Φ (Fin.cons (v.1 + s) v.2)) (D 0 (Fin.cons v.1 v.2)) (v.1 - v.1) := by
          simpa using h
        have h1 := h0.comp_sub_const v.1 v.1
        simp only [add_sub_cancel] at h1
        exact h1.hasFDerivAt)
      (Eventually.of_forall fun v => ih (fun u => Φ (Fin.cons v.1 u)) (fun i u => D i.succ (Fin.cons v.1 u))
        (fun i => (hc i.succ).comp (hcons.comp (continuous_const.prodMk continuous_id)))
        (fun i u => by
          have h := hd i.succ (Fin.cons v.1 u)
          simpa only [Fin.cons_update, Fin.cons_succ] using h) v.2)
      (((ContinuousLinearMap.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hc 0).comp hcons)).continuousAt)
      ((continuous_finsetSum Finset.univ fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) V (ContinuousLinearMap.proj i)).continuous.comp
          ((hc i.succ).comp hcons)).continuousAt)
    let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ i))
    have h2 := HasFDerivAt.comp (f := e) t key.hasFDerivAt e.hasFDerivAt
    have h3 : (↿fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u)) ∘ e = Φ := by
      funext x
      exact congrArg Φ (Fin.cons_self_tail x)
    rw [h3] at h2
    refine h2.congr_fderiv ?_
    ext1 x
    simp [e, HasUncurry.uncurry, Fin.sum_univ_succ, Fin.cons_self_tail]

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]

def pr {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (t : Fin k → ℝ) : G :=
  (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_succ {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by
  simp [pr, List.ofFn_succ]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_zero (γ : Fin 0 → (Multiplicative ℝ →* G)) (t : Fin 0 → ℝ) : pr γ t = 1 := by
  simp [pr]

def Gn (m : ι → G →* A) (γ : Multiplicative ℝ →* G) (Y : ι → A) : Prop :=
  ∀ w (t : ℝ), m w (γ (Multiplicative.ofAdd t)) = NormedSpace.exp (t • Y w)

theorem continuous_pr (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by
  induction k with
  | zero => intro γ _; exact continuous_const.congr fun t => (pr_zero γ t).symm
  | succ k ih =>
    intro γ hγ
    refine Continuous.congr ?_ fun t => (pr_succ γ t).symm
    exact ((hγ 0).comp (continuous_ofAdd.comp (continuous_apply 0))).mul
      ((ih _ fun i => hγ i.succ).comp (continuous_pi fun i => continuous_apply _))

theorem contDiff_exp_smul (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by
  have h : ContDiff ℝ n (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h.comp (contDiff_id.smul contDiff_const)

theorem contDiff_tail (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem contDiff_pr (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by
  induction k with
  | zero => intro γ _; simp only [pr_zero]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro γ hγ
    obtain ⟨h1, h2⟩ := ih (fun i => γ i.succ) fun i => hγ i.succ
    obtain ⟨Y, hY⟩ := hγ 0
    simp only [pr_succ, mul_inv_rev, map_mul, ← map_inv, ← ofAdd_neg, hY w]
    exact ⟨((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0)).mul (h1.comp (contDiff_tail k n)),
      (h2.comp (contDiff_tail k n)).mul ((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0).neg)⟩

def cj (x : G) (γ : Multiplicative ℝ →* G) : Multiplicative ℝ →* G := (MulAut.conj x⁻¹).toMonoidHom.comp γ

omit [TopologicalSpace G] [ContinuousMul G] in
theorem cj_apply (x : G) (γ : Multiplicative ℝ →* G) (s : Multiplicative ℝ) : cj x γ s = x⁻¹ * γ s * x := by
  simp [cj]

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem Gn.cj {m : ι → G →* A} {γ : Multiplicative ℝ →* G} {Y : ι → A} (h : Gn m γ Y) (x : G) :
    Gn m (cj x γ) fun w => m w x⁻¹ * Y w * m w x := by
  intro w t
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : Aˣ := Units.map (m w) (toUnits x⁻¹)
  have h1 : (u : A) = m w x⁻¹ := rfl
  have h2 : ((u⁻¹ : Aˣ) : A) = m w x := by simp [u]
  have := NormedSpace.exp_units_conj u (t • Y w)
  rw [h1, h2] at this
  rw [cj_apply, map_mul, map_mul, h w t, ← this, mul_smul_comm, smul_mul_assoc]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem exists_partial (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by
  induction k with
  | zero => intro γ _ i; exact i.elim0
  | succ k ih =>
    intro γ hγ i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨Y, hY⟩ := hg _ (hγ 0)
      refine ⟨fun t w => m w (pr (fun i => γ i.succ) fun i => t i.succ)⁻¹ * Y w *
        m w (pr (fun i => γ i.succ) fun i => t i.succ), contDiff_pi.2 fun w => ?_, fun t =>
        ⟨_, hcj _ (hγ 0) _, hY.cj _, fun s => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := contDiff_pr m n w k (fun i => γ i.succ) fun i => hg _ (hγ i.succ)
        exact ((h2.comp (contDiff_tail k n)).mul contDiff_const).mul (h1.comp (contDiff_tail k n))
      · simp only [pr_succ, cj_apply, update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true, update_of_ne,
          ofAdd_add, map_mul]
        group
    · obtain ⟨Z, hZ, h⟩ := ih (fun i => γ i.succ) (fun i => hγ i.succ) j
      refine ⟨fun t => Z fun i => t i.succ, hZ.comp (contDiff_tail k n), fun t => ?_⟩
      obtain ⟨γ', h1, h2, h3⟩ := h fun i => t i.succ
      refine ⟨γ', h1, h2, fun s => ?_⟩
      have e : (fun i : Fin k => update t j.succ (t j.succ + s) i.succ) =
          update (fun i : Fin k => t i.succ) j (t j.succ + s) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [pr_succ, pr_succ, e, h3, update_of_ne (Fin.succ_ne_zero j).symm, mul_assoc]

theorem contDiff_comp_pr [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 ((hS f hf).1.comp (continuous_const.mul (continuous_pr k γ fun i => hc _ (hγ i))))
  | succ n ih =>
    intro f hf
    choose f' hf'S hf' using fun j => (hS f hf).2 _ (hβ j)
    choose Z hZ hZ' using exists_partial m L hcj hg n k γ hγ
    have hD : ∀ i, ContDiff ℝ n fun t => ∑ j, (c j (Z i t) : ℂ) * f' j (g * pr γ t) := fun i =>
      ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp
        ((LinearMap.toContinuousLinearMap (c j)).contDiff.comp (hZ i))).mul (ih _ (hf'S j))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, hasFDerivAt_of_partials k _ _ (fun i => (hD i).continuous) fun i t => ?_⟩
    · exact ContDiff.sum fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hD i)
    · obtain ⟨γ', h1, h2, h3⟩ := hZ' i t
      simp only [h3, ← mul_assoc]
      exact hl f f' (fun j => ⟨(hS _ (hf'S j)).1, hf' j⟩) γ' h1 _ h2 _

end PositivityTheory.ThKEst.UMGS

end
