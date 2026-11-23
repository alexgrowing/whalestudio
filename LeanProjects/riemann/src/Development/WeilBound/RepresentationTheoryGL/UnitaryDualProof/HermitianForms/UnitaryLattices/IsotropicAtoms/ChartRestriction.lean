import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentativesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhdsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadicalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumsProportionalCard

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.Form.U.Atom

section Transversal

variable {X : Type} [AddCommGroup X]

theorem sum_transversal_add {M : Type} [AddCommMonoid M] {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t :=
  GlobalTheory.T.coset_sum_translate_invariant hHA hT hTr F hF ha

theorem card_smul_sum_eq {M : Type} [AddCommGroup M] [Module ℂ M] {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A)
    {T T' : Finset X} (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hT' : ∀ t ∈ T', t ∈ A) (hTr' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H') (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∀ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, F t := fun s hs =>
    sum_transversal_add hH hT hTr F hF (hT' s hs)
  have h2 : ∀ t ∈ T, ∑ s ∈ T', F (s + t) = ∑ s ∈ T', F s := fun t ht =>
    sum_transversal_add hH' hT' hTr' F hF' (hT t ht)
  have e1 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
  have e2 : ∑ t ∈ T, ∑ s ∈ T', F (s + t) = T.card • ∑ s ∈ T', F s := by
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
  have e3 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, ∑ s ∈ T', F (s + t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← e1, ← e2, e3]

theorem sum_transversal_char {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (χ : X → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b) (hH : ∀ h ∈ H, χ h = 1) {a : X} (ha : a ∈ A) (hne : χ a ≠ 1) :
    ∑ t ∈ T, χ t = 0 := by
  have key := sum_transversal_add hHA hT hTr χ (fun b h hh => by rw [hχ, hH h hh, mul_one]) ha
  simp only [hχ] at key
  rw [← Finset.sum_mul] at key
  have h0 : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

theorem transversal_nonempty {A H : AddSubgroup X} {T : Finset X} (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    T.Nonempty := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hTr 0 A.zero_mem
  exact ⟨t, ht⟩

variable [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_transversal (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  GlobalTheory.T.exists_finite_coset_representatives A H hA hH hHA

theorem isCompact_sup (A B : AddSubgroup X) (hA : IsCompact (A : Set X)) (hB : IsCompact (B : Set X)) :
    IsCompact ((A ⊔ B : AddSubgroup X) : Set X) :=
  GlobalTheory.T.isCompact_sup_addSubgroup A B hA hB

theorem relIndex_ne_zero' (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    H.relIndex A ≠ 0 :=
  GlobalTheory.T.relIndex_open_compact_ne_zero A H hA hH hHA

end Transversal

section Forms

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem apply_eq_zero_of_isotropic (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hB' : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 :=
  GlobalTheory.T.hermitian_semidefinite_null_radical B hB hB' x hx w

theorem eq_zero_of_diag (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v, B v v = 0) : B = 0 :=
  GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero B hB

end Forms

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ker_char (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} :=
  GlobalTheory.T.isOpen_additive_character_kernel ψ hψ

theorem exists_lat_mem (n : ℕ) (x : Fin n → k) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ x ∈ A :=
  GlobalTheory.T.exists_compact_open_subgroup_mem n x

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) : IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} :=
  GlobalTheory.T.isOpen_character_annihilator ψ hψ n A hA

theorem exists_small_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (n : ℕ) (S : Set (Fin n → k))
    (hS : S ∈ nhds (0 : Fin n → k)) : ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S :=
  GlobalTheory.T.annihilator_compact_within_nhds ψ hψ hψ1 n S hS

theorem comap_lat (n : ℕ) (g : Matrix (Fin n) (Fin n) k) (hg : IsUnit g) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) (hA' : IsOpen (A : Set (Fin n → k))) :
    IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧
      IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) :=
  GlobalTheory.T.isCompact_isOpen_comap_mulVecLin n g hg A hA hA'

end Local

theorem exists_GL_vecMul {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 :=
  GlobalTheory.T.exists_GL_vecMul_eq_last_basis n ξ hξ

end PositivityTheory.RgUd.Form.U.Atom
