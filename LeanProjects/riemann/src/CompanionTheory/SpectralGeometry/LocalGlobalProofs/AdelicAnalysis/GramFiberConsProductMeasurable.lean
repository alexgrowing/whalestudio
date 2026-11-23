import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem corner_half_trace_of_pure_tensor (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (r : R)
    (h : S 0 0 = r ⊗ₜ[F] (1 : E)) : s0 R S = r := by
  rcases subsingleton_or_nontrivial R with h' | h'
  · exact Subsingleton.elim _ _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hK : Module.finrank R (R ⊗[F] E) = 2 := by rw [Module.finrank_baseChange]; exact hfr
  have hc : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := rfl
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    have : (2 : R) = algebraMap F R 2 := (map_ofNat (algebraMap F R) 2).symm
    rw [this, ← map_mul]; simp
  unfold s0
  rw [h, hc, Algebra.trace_algebraMap, hK, two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

variable [NumberField E]

theorem gram_symm (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) (p q : Fin n) :
    sigR R σ (gramR R σ J X q p) = gramR R σ J X p q := by
  simp only [gramR, hR, hform, JR, map_sum, map_mul, hinv, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : sigR R σ (inclR R (J j i)) = inclR R (J i j) := by
    rw [← hJ i j]; simp [sigR, inclR]
  rw [h]; ring

theorem schurM_mem (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS : sigR R σ ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j.succ i.succ) =
      (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ := S.2 i.succ j.succ
  have hi : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, hS, hi]
  ring

end Alg

theorem unit_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {t : F} (ht : t ≠ 0) (u : Rˣ) :
    ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * (((u : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t)) : R ⊗[F] E) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, ← map_mul, inv_mul_cancel₀ ht, map_one]
  rfl

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨-, -, -, -, hart, hred, -⟩ := D.hR
  haveI := hart
  haveI := hred
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have ht : t ≠ 0 := D.ht
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t ht
  refine ⟨?_, ?_⟩
  · intro x hx c X S hS
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R ((a x : Rˣ) : R) c X
    rw [← hS] at h00 h0j hij
    have hx0 : (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = x ⊗ₜ[F] (1 : E) := by
      rw [h00, ← D.hsq x hx]
    have hs0 := corner_half_trace_of_pure_tensor R hfr _ x hx0
    have hc : cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c := by
      funext j
      simp only [cvec]
      rw [hs0, h0j j, ← mul_assoc, unit_tmul ht, one_mul]
    refine ⟨hs0, hc, ?_⟩
    rw [schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
    ext i j
    simp only [schurM]
    rw [hc, hij i j, add_sub_cancel_left]
  · intro S X hB hX
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R
      ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R)
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X
    have hH := gram_symm R σ hinv hJ'.1 (vec
      (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X)
    obtain ⟨r, hr⟩ := hfix ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) (S.2 0 0)
    have hsr := corner_half_trace_of_pure_tensor R hfr _ r hr
    have hrow : ∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec
        (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) 0 j.succ =
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      intro j
      rw [h0j j]
      simp only [cvec]
      rw [← mul_assoc, mul_comm (_ ⊗ₜ[F] (algebraMap F E t)), unit_tmul ht, one_mul]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [h00, hr, ← D.hsq _ hB, hsr]
      · exact hrow j
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [← hH i.succ 0, hrow i]
        exact S.2 i.succ 0
      · rw [hij i j, congrFun (congrFun hX i) j, schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
        simp only [schurM]
        rw [add_sub_cancel]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
