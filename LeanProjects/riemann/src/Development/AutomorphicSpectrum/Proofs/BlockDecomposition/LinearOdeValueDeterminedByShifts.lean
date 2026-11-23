import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinearODE

noncomputable def companion (p : Polynomial ℂ) (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    if h : (i : ℕ) + 1 < n then LinearMap.proj ⟨i + 1, h⟩
    else - ∑ k : Fin n, p.coeff k • LinearMap.proj k

theorem top_eq {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) (s : ℝ) :
    F p.natDegree s = - ∑ k : Fin p.natDegree, p.coeff k * F k s := by
  have h := hrel s
  rw [Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
  have e : ∑ k : Fin p.natDegree, p.coeff k * F k s =
      ∑ k ∈ Finset.range p.natDegree, p.coeff k * F k s :=
    (Finset.sum_range (fun k => p.coeff k * F k s)).symm
  rw [e]
  linear_combination h

theorem lower_eq_zero {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k < p.natDegree, F k = 0 := by
  let X : ℝ → (Fin p.natDegree → ℂ) := fun s i => F i s
  have hX : ∀ s, HasDerivAt X (companion p p.natDegree (X s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have e : companion p p.natDegree (X s) i = F (i + 1) s := by
      simp only [companion, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · have hi : (i : ℕ) + 1 = p.natDegree := by
          have := i.isLt
          omega
        rw [hi, top_eq hp hrel s]
        simp [X, LinearMap.sum_apply, smul_eq_mul]
    rw [e]
    exact hF i s
  have hA : LipschitzWith ‖LinearMap.toContinuousLinearMap (companion p p.natDegree)‖₊
      (companion p p.natDegree) := by
    have := (LinearMap.toContinuousLinearMap (companion p p.natDegree)).lipschitz
    simpa using this
  have hzero : ∀ s, X s = 0 := by
    intro s
    have key := ODE_solution_unique_of_mem_Icc (v := fun _ => companion p p.natDegree)
      (s := fun _ => Set.univ) (a := -(|s| + 1)) (b := |s| + 1) (t₀ := 0)
      (fun t _ => hA.lipschitzOnWith)
      ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
      (fun t _ => (hX t).continuousAt.continuousWithinAt) (fun t _ => hX t)
      (fun _ _ => Set.mem_univ _)
      (continuousOn_const (c := (0 : Fin p.natDegree → ℂ)))
      (fun t _ => by simpa using hasDerivAt_const t (0 : Fin p.natDegree → ℂ))
      (fun _ _ => Set.mem_univ _)
      (by funext i; simpa [X] using h0 i i.isLt)
    exact key ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  intro k hk
  funext s
  simpa [X] using congrFun (hzero s) ⟨k, hk⟩

theorem chain_zero {F : ℕ → ℝ → ℂ} (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    {m : ℕ} (h : F m = 0) : ∀ k, m ≤ k → F k = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hmk ih =>
    funext s
    have h1 := hF k s
    rw [ih] at h1
    show F (k + 1) s = 0
    exact h1.unique (hasDerivAt_const s (0 : ℂ))

theorem eq_zero_of_initial {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k, F k = 0 := by
  have hlow := lower_eq_zero hp hF hrel h0
  have htop : F p.natDegree = 0 := by
    funext s
    rw [top_eq hp hrel s]
    have hz : ∀ k : Fin p.natDegree, p.coeff k * F k s = 0 := fun k => by
      rw [hlow k k.isLt]
      simp
    simp [hz]
  intro k
  rcases lt_or_ge k p.natDegree with hk | hk
  · exact hlow k hk
  · exact chain_zero hF htop k hk

def solSpace (p : Polynomial ℂ) : Submodule ℂ (ℕ → ℝ → ℂ) where
  carrier := {F | (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) ∧
    ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0}
  add_mem' := by
    rintro F G ⟨hF, rF⟩ ⟨hG, rG⟩
    refine ⟨fun k s => (hF k s).add (hG k s), fun s => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, rF s, rG s, add_zero]
  zero_mem' := ⟨fun k s => hasDerivAt_const s (0 : ℂ), fun s => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, rF⟩
    refine ⟨fun k s => (hF k s).const_mul c, fun s => ?_⟩
    have h : ∀ k, p.coeff k * (c • F) k s = c * (p.coeff k * F k s) := fun k => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, ← Finset.mul_sum, rF s, mul_zero]

theorem finiteDimensional_solSpace {p : Polynomial ℂ} (hp : p.Monic) :
    FiniteDimensional ℂ (solSpace p) := by
  let Φ : solSpace p →ₗ[ℂ] (Fin p.natDegree → ℂ) :=
    { toFun := fun F i => (F : ℕ → ℝ → ℂ) i 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun F hF => ?_)
  obtain ⟨hFd, hFr⟩ := F.2
  have hz := eq_zero_of_initial hp hFd hFr (fun k hk => congrFun hF ⟨k, hk⟩)
  exact Subtype.ext (funext hz)

theorem deriv_zero_eq_sum :
    ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ,
      (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) →
      (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) →
      F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  intro p hp
  haveI := finiteDimensional_solSpace hp
  let ev : ℝ → Module.Dual ℂ (solSpace p) := fun t =>
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 0 t
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  let φ : Module.Dual ℂ (solSpace p) :=
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 1 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_dualCoannihilator] at hF
    have h0 : (F : ℕ → ℝ → ℂ) 0 = 0 :=
      funext fun t => hF (ev t) (Submodule.subset_span ⟨t, rfl⟩)
    obtain ⟨hFd, -⟩ := F.2
    have hall := chain_zero hFd h0
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun k => hall k (Nat.zero_le k))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hco,
      Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφ
  refine ⟨c.support, c, fun F hFd hFr => ?_⟩
  have hmem : F ∈ solSpace p := ⟨hFd, hFr⟩
  have key := LinearMap.congr_fun hc ⟨F, hmem⟩
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply] at key
  exact key.symm

end GlobalTheory.CompanionTheory.LinearODE
