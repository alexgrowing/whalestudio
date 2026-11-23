import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.QdetCoeff

theorem coeff_mem_span_values {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) (a : ℕ → M)
    (f : ℂ → M) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range (n + 1), u ^ k • a k) (k : ℕ) (hk : k ≤ n) :
    a k ∈ Submodule.span ℂ (Set.range f) := by
  set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    simp only [hv, Nat.cast_inj] at h
    exact Fin.ext h
  set V := Matrix.vandermonde v
  have hdet : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set k' : Fin (n + 1) := ⟨k, by omega⟩
  have key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k := by
    simp_rw [hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j := by
      intro j
      rw [← hWV, Matrix.mul_apply]
      rfl
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [k']
  rw [← key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in

theorem qdet_eq_sum_coeff {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (w : ℂ) :
    Formalism.REAL.qdet E w = ∑ j ∈ Finset.range (n + 1), w ^ j • (qdetPoly E).coeff j := by
  rw [← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdetPoly_coeff_top {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    (qdetPoly E).coeff n = 1 := by
  rw [coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]

theorem qdet_shift_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ),
    ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  intro A _ _ n X c
  set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb
  set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
    intro u
    rw [qdet_eq_sum_coeff]
    have hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j =
        ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ)) := by
      intro j hj
      rw [add_pow]
      have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        have hj' := Finset.mem_range.mp hj
        intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]
    simp_rw [ha, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine ⟨a, ?_, ?_, hexp⟩
  · simp only [ha]
    rw [Finset.sum_eq_single n]
    · simp [hb, qdetPoly_coeff_top]
    · intro j hj hjn
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · intro k
    by_cases hk : k ≤ n
    · exact coeff_mem_span_values n a _ hexp k hk
    · have : a k = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [this]; exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.CTFin.QdetCoeff
