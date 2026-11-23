import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusChainCarry
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.Xgn.A_xgr_r_om

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  rw [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have he : (r • fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C (r * χ a) := by
    funext a
    simp [Algebra.smul_def, map_mul]
  rw [he]

theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  exact hv.le_of_dvd (Ideal.mem_span_singleton.mp h)

theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) := by
  apply le_antisymm
  · apply v_le_of_mem hv
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  · apply v_le_of_mem hv
    rw [h]
    exact Ideal.mem_span_singleton_self b

theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  have key : ∀ x y : X → C, v (l x) ≤ b → v (l y) ≤ b → v (l (x + y)) ≤ b := by
    intro x y hx hy
    rw [map_add]
    exact le_trans (v.map_add _ _) (max_le hx hy)
  have ksm : ∀ (r : R) (x : X → C), v (l x) ≤ b → v (l (r • x)) ≤ b := by
    intro r x hx
    rw [map_smul, Algebra.smul_def, map_mul]
    exact le_trans (mul_le_of_le_one_left (by positivity) (hv.map_le_one r)) hx
  have k0 : v (l 0) ≤ b := by simp
  have step : ∀ g ∈ Submodule.span R s, ∀ g' ∈ Submodule.span R s, v (l (g * g')) ≤ b := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | mem y hy => exact h x hx y hy
      | zero => simpa using k0
      | add y z _ _ hy hz => rw [mul_add]; exact key _ _ hy hz
      | smul r y _ hy => rw [mul_smul_comm]; exact ksm r _ hy
    | zero => simpa using k0
    | add x z _ _ hx hz => rw [add_mul]; exact key _ _ hx hz
    | smul r x _ hx => rw [smul_mul_assoc]; exact ksm r _ hx
  intro g hg
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, f', hf', rfl⟩ := hx
    exact step f hf f' hf'
  | zero => exact k0
  | add x z _ _ hx hz => exact key _ _ hx hz
  | smul r x _ hx => exact ksm r _ hx

variable [Fintype F] [DecidableEq F]

theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hg ⊢
  refine ⟨?_, by simp [Pi.pow_apply, hg.2]⟩
  induction k with
  | zero => simpa using hg.1
  | succ n ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg.1

theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨(mem_x_ideal_iff _ χ c).mp hc, ?_⟩
    simp [MulChar.map_nonunit χ not_isUnit_zero]
  have he : (fun a => algebraMap R C (c ^ (j + 2) * (χ ^ (j + 2)) a)) =
      (fun a => algebraMap R C (c * χ a)) * (fun a => algebraMap R C (c * χ a)) ^ (j + 1) := by
    funext a
    simp only [Pi.mul_apply, Pi.pow_apply, MulChar.pow_apply' χ (by omega : j + 2 ≠ 0), map_pow,
      map_mul]
    ring
  rw [he]
  unfold sqIdeal
  exact Submodule.subset_span ⟨_, hg, _, pow_mem_aug AA hg j, rfl⟩

theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  unfold sqIdeal
  rw [Submodule.span_le]
  rintro h ⟨f, hf, f', hf', rfl⟩
  exact AA.mul_mem f f' ((mem_aug _ f).mp hf).1 ((mem_aug _ f').mp hf').1

omit [Fintype F] [DecidableEq F] in
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      rcases f with _ | f <;> simp at h2 <;> omega
    · exact h0
  have key : ∀ (g : ℕ) (m : ℕ), m < p ^ g →
      ∃ d : Fin g → Fin p, ∑ n : Fin g, (d n : ℕ) * p ^ (n : ℕ) = m := by
    intro g
    induction g with
    | zero =>
      intro m hm
      refine ⟨Fin.elim0, ?_⟩
      simp at hm
      simp [hm]
    | succ g ih =>
      intro m hm
      obtain ⟨d', hd'⟩ := ih (m / p) (by
        rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]
        exact hm)
      refine ⟨Fin.cons ⟨m % p, Nat.mod_lt _ hp⟩ d', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      have hs : ∑ x : Fin g, (d' x : ℕ) * p ^ ((x : ℕ) + 1) =
          (∑ x : Fin g, (d' x : ℕ) * p ^ (x : ℕ)) * p := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [hs, hd']
      exact Nat.mod_add_div' m p
  obtain ⟨d, hd⟩ := key f m h2
  refine ⟨d, ?_, hd⟩
  by_contra hne
  push_neg at hne
  have hz : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 :=
    Finset.sum_eq_zero (fun n _ => by simp [hne n])
  omega

theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end PositivityTheory.Xgn.A_xgr_r_om
