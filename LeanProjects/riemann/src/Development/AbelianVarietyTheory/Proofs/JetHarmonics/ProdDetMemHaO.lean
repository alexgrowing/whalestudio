import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude

namespace GlobalTheory.CombMinor

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]

def cMat (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Letter Ty r n) k) :=
  Matrix.of fun ρ i : Fin s => ∑ b, C (B ρ b) * (X ⟨τ, Fin.castLE hs i, b⟩ : MvPolynomial (Letter Ty r n) k)

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {s : ℕ} (M : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun π _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem cMat_supported (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (S : Set (Letter Ty r n))
    (h : ∀ ρ i b, B ρ b ≠ 0 → (⟨τ, i, b⟩ : Letter Ty r n) ∈ S) :
    (cMat τ s hs B).det ∈ supported k S := by
  refine det_mem (supported k S).toSubring _ fun ρ i => ?_
  change _ ∈ supported k S
  simp only [cMat, Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun b _ => ?_
  by_cases hb : B ρ b = 0
  · rw [hb, C_0, zero_mul]; exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨_, h ρ _ b hb, rfl⟩

theorem cMat_range (O : Subring k) (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (h : ∀ ρ b, B ρ b ∈ O) :
    (cMat τ s hs B).det ∈ (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range := by
  refine det_mem _ _ fun ρ i => ?_
  simp only [cMat, Matrix.of_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ⟨C ⟨B ρ b, h ρ b⟩, by simp⟩ ⟨X _, map_X _ _⟩

theorem cMat_rowShift [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (σ : Ty) (i i' : Fin (r σ)) (hii : i' < i) (t : k) :
    rowShift r n k σ i i' t (cMat τ s hs B).det = (cMat τ s hs B).det := by
  rw [AlgHom.map_det]
  by_cases hτ : τ = σ
  · subst hτ
    by_cases hin : i.val < s
    · have hin' : i'.val < s := lt_trans hii hin
      let i0 : Fin s := ⟨i.val, hin⟩
      let i1 : Fin s := ⟨i'.val, hin'⟩
      have hne : i0 ≠ i1 := by
        intro h
        have := congrArg Fin.val h
        simp only [i0, i1] at this
        exact (ne_of_gt hii) (Fin.ext this)
      have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) =
          (cMat τ s hs B).updateCol i0 (fun p => cMat τ s hs B p i0 +
            (C t : MvPolynomial (Letter Ty r n) k) • cMat τ s hs B p i1) := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, Matrix.updateCol_apply, crSig_iff]
        by_cases hp : q = i0
        · subst hp
          have hc : Fin.castLE hs i0 = i := Fin.ext rfl
          have hc1 : Fin.castLE hs i1 = i' := Fin.ext rfl
          simp only [hc, hc1, if_true, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
        · rw [if_neg hp]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [if_neg]
          intro h
          apply hp
          apply Fin.ext
          have := congrArg Fin.val h
          simp only [Fin.val_castLE] at this
          exact this
      rw [hmat]
      exact Matrix.det_updateCol_add_smul_self _ hne (C t)
    · have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, crSig_iff]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        omega
      rw [hmat]
  · have hmat : (rowShift r n k σ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
      refine Matrix.ext fun p q => ?_
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
        algHom_C, algebraMap_eq, rowShift, aeval_X]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_neg (crSig_ne hτ)]
    rw [hmat]

theorem cMat_hom [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (σ : Ty) (i0 : ℕ) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i0) (cMat τ s hs B).det
      (if τ = σ ∧ i0 < s then 1 else 0) := by
  rw [← mem_weightedHomogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← crRowSum τ σ s i0]
  refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [cMat, Matrix.of_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [C_mul']
  refine Submodule.smul_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_X k (crW (r := r) (n := n) σ i0) ⟨τ, Fin.castLE hs j, b⟩

theorem prod_det_mem_HaO : ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (O : Subring k) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (A : Type) [Fintype A] (σ : A → Ty) (s : A → ℕ) (hs : ∀ α, s α ≤ r (σ α)) (B : ∀ α, Fin (s α) → Fin n → k) (e : A → ℕ), (∀ α ρ b, B α ρ b ∈ O) → (∀ τ, cc τ ≠ τ) → (∀ α α', e α ≠ 0 → e α' ≠ 0 → σ α' = cc (σ α) → ∀ ρ ρ' b, B α ρ b = 0 ∨ B α' ρ' b = 0) → (∀ (τ : Ty) (i : Fin (r τ)), ∑ α ∈ Finset.univ.filter (fun α => σ α = τ ∧ i.val < s α), e α = a τ i) → (∏ α, (Matrix.of fun ρ i : Fin (s α) => ∑ b, MvPolynomial.C (B α ρ b) * (MvPolynomial.X ⟨σ α, Fin.castLE (hs α) i, b⟩ : MvPolynomial (Letter Ty r n) k)).det ^ e α) ∈ HaO r n k O cc isX a := by
  intro Ty _ r n k _ O cc isX a A _ σ s hs B e hO _ hdis hdeg
  change (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · let S : Set (Letter Ty r n) := {ℓ | ∃ α, e α ≠ 0 ∧ σ α = ℓ.1 ∧ ∃ ρ, B α ρ ℓ.2.2 ≠ 0}
    have hS : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ supported k S := by
      refine Subalgebra.prod_mem _ fun α _ => ?_
      by_cases he : e α = 0
      · rw [he, pow_zero]; exact Subalgebra.one_mem _
      · exact Subalgebra.pow_mem _ (cMat_supported _ _ _ _ S fun ρ i b hb =>
          (show _ ∈ S from ⟨α, he, rfl, ρ, hb⟩)) _
    generalize (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) = P at hS
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
    intro τ _ i i'
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
    by_cases hb : b = b'
    · subst hb
      have key : pderiv (⟨τ, i, b⟩ : Letter Ty r n) (pderiv (⟨cc τ, i', b⟩ : Letter Ty r n) P) = 0 := by
        by_cases hg : (⟨cc τ, i', b⟩ : Letter Ty r n) ∈ S
        · have hg' : (⟨τ, i, b⟩ : Letter Ty r n) ∉ S := by
            rintro ⟨α, he, hσ, ρ, hρ⟩
            obtain ⟨α', he', hσ', ρ', hρ'⟩ := hg
            rcases hdis α α' he he' (by rw [hσ', hσ]) ρ ρ' b with h | h
            · exact hρ h
            · exact hρ' h
          exact pderiv_eq_zero_of_notMem_vars
            (fun hv => hg' (mem_supported.1 (crPderiv_supported _ hS) hv))
        · rw [pderiv_eq_zero_of_notMem_vars (fun hv => hg (mem_supported.1 hS hv)), map_zero]
      simpa using congrArg (fun x => (1 : k) • x) key
    · simp [Matrix.one_apply_ne hb]
  · intro τ i i' hii t
    rw [map_prod]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [map_pow, cMat_rowShift _ _ _ _ _ _ _ hii]
  · intro m hm τ i
    rw [← crW_weight]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun α => (cMat (σ α) (s α) (hs α) (B α)).det ^ e α)
      (fun α => e α • (if σ α = τ ∧ i.val < s α then 1 else 0))
      (fun α _ => (cMat_hom (σ α) (s α) (hs α) (B α) τ i.val).pow (e α))
    rw [h (Finsupp.mem_support_iff.1 hm), ← hdeg τ i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> simp
  · intro m
    obtain ⟨Q, hQ⟩ : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈
        (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range :=
      Subring.prod_mem _ fun α _ => Subring.pow_mem _ (cMat_range O _ _ _ _ (hO α)) _
    rw [← hQ, coeff_map]
    exact (Q.coeff m).2

end GlobalTheory.CombMinor
