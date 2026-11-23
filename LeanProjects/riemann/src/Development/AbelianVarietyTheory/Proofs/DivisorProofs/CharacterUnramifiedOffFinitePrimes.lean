import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOff

theorem natCast_not_mem {D : D7} {S : Finset ℕ} {w : Pl D.host.E} (hw : Off S w) {N : ℕ} (hN : 0 < N)
    (hS : N.primeFactors ⊆ S) : ((N : 𝓞 D.host.E)) ∉ w.asIdeal := by
  intro h
  rw [← Nat.prod_factorization_pow_eq_self hN.ne', Nat.cast_finsuppProd] at h
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  dsimp only at hpw
  rw [Nat.cast_pow] at hpw
  exact hw p (hS (Nat.support_factorization N ▸ hp)) (w.isPrime.mem_of_pow_mem _ hpw)

theorem infPart_idem {D : D7} {e : AE D} (he : Formalism.L2.Theta.IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨hee, hec, v, ε, ⟨α, hε, -, -⟩, hs⟩ := he
  have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hs, mul_add, hee, hec, add_zero]
  have h2 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    subst hε
    have e1 : (algebraMap (AF D.host.F) (AE D)) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [e1]
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  rw [h1, map_mul, h2, mul_zero]

theorem intAE_one {D : D7} : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x h =>
    obtain ⟨a, ha, s, rfl⟩ := h
    induction hy using AddSubgroup.closure_induction with
    | mem y h' =>
      obtain ⟨b, hb, t, rfl⟩ := h'
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, s * t, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h1 => rw [neg_mul]; exact neg_mem h1

theorem unr_off : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  intro D c hc
  obtain ⟨N, hN, hN1, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N.primeFactors, fun q hq => Nat.prime_of_mem_primeFactors hq, ?_⟩
  intro w hw e he x hx h1 h2
  have hNw := natCast_not_mem hw hN le_rfl
  have hN0 : ((N : 𝓞 D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hg : finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) ∈ intAE D :=
    not_not.1 ((he.2 _ hN0).not.1 hNw)
  have hNE : (((N : 𝓞 D.host.E) : D.host.E)) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : (N : AE D) * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ = 1 := by
    rw [show (N : AE D) = incA D (((N : 𝓞 D.host.E) : D.host.E)) by simp, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  have key : (x : AE D) - 1 = (N : AE D) * (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ * ((x : AE D) - 1)) := by
    linear_combination (-1 : AE D) * hx - (e * ((x : AE D) - 1)) * hi
  refine hN1 x ⟨?_, h1, h2⟩ ⟨finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) * (finPart D (x : AE D) - 1),
    intAE_mul hg (sub_mem h1 intAE_one), ?_⟩
  · have h0 := infPart_idem he.1
    have := congrArg (infPart D) hx
    simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0, zero_mul, zero_add, sub_zero] at this
    exact this.symm
  · have := congrArg (finPart D) key
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at this
    rw [nsmul_eq_mul]
    refine this.trans ?_
    simp only [RingHom.map_mul, map_natCast]

end GlobalTheory.UnrOff
