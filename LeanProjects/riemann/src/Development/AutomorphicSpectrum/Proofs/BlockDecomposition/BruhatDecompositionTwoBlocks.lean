import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import GroundTheory.AutomorphicForms.FiniteBruhat

open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Bruhat

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

theorem pm_eq_permGL (σ : Equiv.Perm (Fin n)) : pm K σ = permGL K σ := rfl

theorem conj_pm_apply (τ : Equiv.Perm (Fin n)) (x : GL (Fin n) K) (i j : Fin n) :
    ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (x : Matrix (Fin n) (Fin n) K) (τ⁻¹ i) (τ⁻¹ j) := by
  rw [pm_eq_permGL, ← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply]

theorem isBlockUT_conj {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    IsBlockUT K b ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  rw [conj_pm_apply]
  refine (mem_borel_iff x).1 hx _ _ ?_
  by_contra hle
  have h : b i ≤ b j := by simpa [Function.comp_apply] using hτ (not_lt.1 hle)
  exact absurd hij (not_lt.2 h)

theorem conj_mem_parab {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    pm K τ * x * (pm K τ)⁻¹ ∈ parab K b := by
  refine ⟨isBlockUT_conj b τ hτ hx, ?_⟩
  have e : (pm K τ * x * (pm K τ)⁻¹)⁻¹ = pm K τ * x⁻¹ * (pm K τ)⁻¹ := by group
  rw [e]
  exact isBlockUT_conj b τ hτ ((borel n K).inv_mem hx)

theorem conj_diag_mem_borel (ρ : Equiv.Perm (Fin n)) {t : GL (Fin n) K}
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) :
    pm K ρ * t * (pm K ρ)⁻¹ ∈ borel n K := by
  refine (mem_borel_iff _).2 fun i j hji => ?_
  rw [conj_pm_apply]
  exact ht _ _ fun e => hji.ne (ρ⁻¹.injective e).symm

theorem exists_diag_mul_uni {y : GL (Fin n) K} (hy : y ∈ borel n K) :
    ∃ t : GL (Fin n) K, (∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∃ u ∈ patSet K (fun i j : Fin n => i < j), y = t⁻¹ * u := by
  have hd := borel_diag_ne_zero hy
  obtain ⟨t, -, htD⟩ := exists_borel_of_isUpperTriangular
    (Matrix.diagonal fun i => ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹)
    (Matrix.blockTriangular_diagonal _) (fun i => by simpa using hd i)
  refine ⟨t, fun i j hij => by rw [htD, Matrix.diagonal_apply_ne _ hij], t * y, ?_, by group⟩
  intro i j
  have hval : ((t * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹ * (y : Matrix (Fin n) (Fin n) K) i j := by
    rw [Units.val_mul, htD, Matrix.diagonal_mul]
  refine ⟨fun e => ?_, fun hne hlt => ?_⟩
  · subst e
    rw [hval, inv_mul_cancel₀ (hd i)]
  · have hji : j < i := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
    rw [hval, (mem_borel_iff y).1 hy i j hji, mul_zero]

theorem bruhat_parab_parab {s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (g : GL (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b', ∃ α ∈ parab K b, g = β * pm K σ * α := by
  set τ := Tuple.sort b
  set τ' := Tuple.sort b'
  obtain ⟨ρ, hρ⟩ := exists_mem_doubleCoset_permGL ((pm K τ')⁻¹ * g * pm K τ)
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.1 hρ
  refine ⟨τ' * ρ * τ⁻¹, _, conj_mem_parab b' τ' (Tuple.monotone_sort b') hx,
    _, conj_mem_parab b τ (Tuple.monotone_sort b) hy, ?_⟩
  have hm : pm K (τ' * ρ * τ⁻¹) = pm K τ' * permGL K ρ * (pm K τ)⁻¹ := by
    simp only [pm_eq_permGL, map_mul, map_inv]
  have hg : g = pm K τ' * (x * permGL K ρ * y) * (pm K τ)⁻¹ := by
    rw [← hxy]; group
  rw [hm, hg]
  group

theorem bruhat_parab_uni {s : ℕ} (b : Fin n → Fin s) (g : GL (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b, ∃ u ∈ patSet K (fun i j : Fin n => i < j),
      g = β * pm K σ * u := by
  set τ := Tuple.sort b
  obtain ⟨ρ, hρ⟩ := exists_mem_doubleCoset_permGL ((pm K τ)⁻¹ * g)
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.1 hρ
  obtain ⟨t, ht, u, hu, hyu⟩ := exists_diag_mul_uni hy
  have hw := conj_diag_mem_borel ρ ht
  have hb : x * (pm K ρ * t * (pm K ρ)⁻¹)⁻¹ ∈ borel n K :=
    (borel n K).mul_mem hx ((borel n K).inv_mem hw)
  refine ⟨τ * ρ, _, conj_mem_parab b τ (Tuple.monotone_sort b) hb, u, hu, ?_⟩
  have hm : pm K (τ * ρ) = pm K τ * pm K ρ := by
    simp only [pm_eq_permGL, map_mul]
  have hg : g = pm K τ * (x * pm K ρ * (t⁻¹ * u)) := by
    rw [← hyu, pm_eq_permGL ρ, ← hxy]; group
  rw [hm, hg]
  group

theorem bruhatTwo : ReciprocityTheory.Ty.Fin.St.BruhatTwo :=
  fun _ _ _ _ _ => ⟨fun _ _ b b' g => bruhat_parab_parab b b' g,
    fun _ b g => bruhat_parab_uni b g⟩

end GlobalTheory.CompanionTheory.TyFin.Bruhat
