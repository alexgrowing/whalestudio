import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewPairing

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (x : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = algebraMap F R (Algebra.trace F E x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

variable {D : D7}

theorem trace_incA (x : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D x) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) :=
  trace_one_tmul x

theorem cA_smul (c : AF D.host.F) (a : AE D) : cA D (c • a) = c • cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem trace_star (x : D.host.E) :
    Algebra.trace D.host.F D.host.E (star x) = Algebra.trace D.host.F D.host.E x :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective D.sp.cm.sig D.sp.cm.sig.bijective) x

theorem eq_zero_of_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {q : D.host.F}
    (h : ∀ t : AF D.host.F, ψ (t * algebraMap D.host.F (AF D.host.F) q) = 1) : q = 0 := by
  by_contra hq
  obtain ⟨I, hI, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField D.host.F)
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ ⟨I, hP, hI⟩
  have h1 := h (pairA D.host.F 0 (singleV D.host.F ⟨I, hP, hI⟩ y) * algebraMap D.host.F (AF D.host.F) q⁻¹)
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, mul_one] at h1
  exact hy h1

theorem skew_perfect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (M : Matrix (Fin ρ) (Fin ρ) D.host.E), Mᴴ = -M → (∀ c : skewA D ρ, ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((rat M : Mx D ρ ρ) ⬝ c.1).trace) = 1) → M = 0 := by
  intro D ψ hψ ρ M hM h
  have key : ∀ A : Matrix (Fin ρ) (Fin ρ) D.host.E, Algebra.trace D.host.F D.host.E (M * A).trace = 0 := by
    intro A
    refine eq_zero_of_char hψ fun t => ?_
    have hN : adj (rat (A - Aᴴ) : Mx D ρ ρ) = -rat (A - Aᴴ) := by
      rw [← rat_conjTranspose, ← rat_neg, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
    have hc : t • (rat (A - Aᴴ) : Mx D ρ ρ) ∈ skewA D ρ := by
      rw [mem_skewA, ← smul_neg, ← hN]
      funext i j
      exact cA_smul t (rat (A - Aᴴ) j i)
    have h1 := h ⟨_, hc⟩
    have e1 : (M * (A - Aᴴ)).trace = (M * A).trace + star (M * A).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hM, Matrix.mul_neg, trace_neg, trace_mul_comm Aᴴ, Matrix.mul_sub,
        trace_sub, sub_eq_add_neg]
    have e2 : ((rat M : Mx D ρ ρ) ⬝ (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace = t • incA D (M * (A - Aᴴ)).trace := by
      rw [Matrix.mul_smul, trace_smul, ← rat_mul, AddMonoidHom.map_trace (incA D)]
      rfl
    have e3 : algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D)
        ((rat M : Mx D ρ ρ) ⬝ (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace =
        t * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E (M * A).trace) := by
      rw [e2, map_smul, trace_incA, e1, map_add, trace_star, smul_eq_mul, mul_left_comm, ← map_mul]
      congr 2
      ring
    rw [← e3]
    exact h1
  funext j i
  refine (traceForm_nondegenerate D.host.F D.host.E).1 (M j i) fun s => ?_
  have := key (Matrix.single i j s)
  rwa [trace_mul_single] at this

end GlobalTheory.SkewPairing
