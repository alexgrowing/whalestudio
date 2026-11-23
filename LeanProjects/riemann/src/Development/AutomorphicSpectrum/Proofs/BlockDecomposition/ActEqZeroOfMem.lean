import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem rhoVec_sub {i j : Fin n} (h : (j : ℕ) = i + 1) : rhoVec n i - rhoVec n j = 1 := by
  have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast h
  simp only [rhoVec, this]; ring

def sqSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (i j : Fin n), (j : ℕ) = i + 1 ∧ u * e (j, i) ^ 2 = x}

def Jp (n : ℕ) : Submodule ℂ (U n) := vermaIdeal (rhoVec n) ⊔ sqSpan n

theorem vermaIdeal_le_Jp : vermaIdeal (rhoVec n) ≤ Jp n := le_sup_left

theorem sqSpan_le_Jp : sqSpan n ≤ Jp n := le_sup_right

theorem mul_mem_sqSpan (v : U n) {x : U n} (hx : x ∈ sqSpan n) : v * x ∈ sqSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, i, j, hij, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_Jp (v : U n) {x : U n} (hx : x ∈ Jp n) : v * x ∈ Jp n := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem _ (vermaIdeal_le_Jp (mul_mem_vermaIdeal _ v hy))
    (sqSpan_le_Jp (mul_mem_sqSpan v hw))

theorem mul_sq_mem_Jp (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ Jp n :=
  sqSpan_le_Jp (Submodule.subset_span ⟨u, i, j, hij, rfl⟩)

def IsAdW (μ : Fin n → ℤ) (x : U n) : Prop :=
  ∀ k, e (k, k) * x - x * e (k, k) = (μ k : ℂ) • x

def LowExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a ∈ m.support, IsLower a

def lowSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ canon m = x}

def lowSpanW (μ : Fin n → ℤ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ ∧ canon m = x}

def casC (τ : Fin n → ℂ) : ℂ :=
  ∑ a, τ a ^ 2 + ∑ a, ∑ b, if a < b then τ a - τ b else 0

def ht (μ : Fin n → ℤ) : ℤ := ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℕ)) * μ k

theorem exists_act {A : Type} [AddCommGroup A] [Module ℂ A] (G : Fin n → Fin n → Module.End ℂ A)
    (h : Formalism.REAL.GlRel G) : ∃ φ : U n →ₐ[ℂ] Module.End ℂ A, ∀ i j, φ (e (i, j)) = G i j := by
  let L : gl n →ₗ[ℂ] Module.End ℂ A :=
    { toFun := fun X => ∑ a : Fin n × Fin n, X a.1 a.2 • G a.1 a.2
      map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Finset.smul_sum, smul_smul] }
  have hL : ∀ a : Fin n × Fin n, L (E a) = G a.1 a.2 := by
    intro a
    show ∑ b : Fin n × Fin n, (E a) b.1 b.2 • G b.1 b.2 = _
    rw [Finset.sum_eq_single a]
    · simp [E]
    · intro b _ hb
      have : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hb (Prod.ext h.1 h.2).symm
      simp [E, Matrix.single_apply, this]
    · simp
  have hE : ∀ a b : Fin n × Fin n, L ⁅E a, E b⁆ = ⁅L (E a), L (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul,
      hL, hL, h, map_sub, apply_ite L, apply_ite L, hL, hL, map_zero]
  let ρ : gl n →ₗ⁅ℂ⁆ Module.End ℂ A :=
    { L with
      map_lie' := fun {X Y} => by
        show L ⁅X, Y⁆ = ⁅L X, L Y⁆
        rw [eq_sum_E X, eq_sum_E Y]
        simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ ρ, fun i j => ?_⟩
  rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hL (i, j)

theorem act_word {A : Type} [AddCommGroup A] [Module ℂ A] {G : Fin n → Fin n → Module.End ℂ A}
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (hφ : ∀ i j, φ (e (i, j)) = G i j)
    (l : List (Fin n × Fin n)) : φ (word l) = (l.map fun p => G p.1 p.2).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, map_mul, ih, List.map_cons, List.prod_cons, hφ]

theorem glRel_e (n : ℕ) : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) :=
  fun a b c d => e_mul_sub_mul (a, b) (c, d)

theorem IsAdW.e_mul {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) (a : Fin n × Fin n) :
    IsAdW (fun k => μ k + rootAt a k) (e a * x) := by
  intro k
  have h1 := e_diag_mul_sub k a
  have h2 := hx k
  have : e (k, k) * (e a * x) - e a * x * e (k, k) =
      (e (k, k) * e a - e a * e (k, k)) * x + e a * (e (k, k) * x - x * e (k, k)) := by
    noncomm_ring
  rw [this, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  push_cast; ring_nf

theorem ht_rootAt (a : Fin n × Fin n) :
    ht (rootAt a) = 2 * ((a.2 : ℕ) : ℤ) - 2 * ((a.1 : ℕ) : ℤ) := by
  simp only [ht, rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ht_add_rootAt (μ : Fin n → ℤ) (a : Fin n × Fin n) :
    ht (fun k => μ k + rootAt a k) = ht μ + ht (rootAt a) := by
  simp only [ht, mul_add, Finset.sum_add_distrib]

theorem ht_wt (m : Fin n × Fin n →₀ ℕ) :
    ht (wt m) = m.sum fun a c => (c : ℤ) * ht (rootAt a) := by
  simp only [ht, wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ht_wt_nonpos {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ht (wt m) ≤ 0 := by
  rw [ht_wt]
  refine Finset.sum_nonpos fun a ha => ?_
  have h : (a.2 : ℕ) < a.1 := hm a ha
  show (m a : ℤ) * ht (rootAt a) ≤ 0
  rw [ht_rootAt]
  have : (0 : ℤ) ≤ (m a : ℤ) := by positivity
  nlinarith

theorem act_eq_zero_of_mem {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) {x : U n}
    (hx : x ∈ vermaIdeal (rhoVec n)) : φ x t = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  have h1 : φ y t = 0 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      simp [hu a ha]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have h2 : φ w t = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, k, rfl⟩ := hx
      simp [hd k, Algebra.algebraMap_eq_smul_one]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  simp [h1, h2]

end GlobalTheory.CompanionTheory.PresRho
