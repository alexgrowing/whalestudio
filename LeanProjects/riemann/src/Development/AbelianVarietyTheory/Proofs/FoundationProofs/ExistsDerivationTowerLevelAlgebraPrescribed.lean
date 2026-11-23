import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjectiveStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

section Gen
variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]
  [Module Sᵐᵒᵖ M] [IsCentralScalar S M]

def sqEv (z q : S) (μ ν : M) : Polynomial (Polynomial A) →+* TrivSqZeroExt S M :=
  eval₂RingHom (eval₂RingHom ((inlHom S M).comp (algebraMap A S)) (inl z + inr μ)) (inl q + inr ν)

def ev2 (z q : S) : Polynomial (Polynomial A) →+* S :=
  eval₂RingHom (eval₂RingHom (algebraMap A S) z) q

theorem sq_inr (m : M) : (inr m : TrivSqZeroExt S M) ^ 2 = 0 := by
  rw [pow_two, inr_mul_inr]

theorem sqEv_C (z q : S) (μ ν : M) (g : Polynomial A) :
    sqEv z q μ ν (C g) = inl (eval₂ (algebraMap A S) z g) +
      inr (eval₂ (algebraMap A S) z (derivative g) • μ) := by
  simp only [sqEv, coe_eval₂RingHom, eval₂_C]
  rw [eval₂_eq_eval_map, eval_add_of_sq_eq_zero _ _ _ (sq_inr μ), derivative_map,
    ← eval₂_eq_eval_map, ← eval₂_eq_eval_map]
  rw [show (inl z : TrivSqZeroExt S M) = inlHom S M z from rfl, ← hom_eval₂, ← hom_eval₂,
    inlHom_apply, inlHom_apply, inl_mul_inr]

theorem sqEv_X (z q : S) (μ ν : M) : sqEv (A := A) z q μ ν X = inl q + inr ν := by
  simp [sqEv]

theorem fst_sqEv (z q : S) (μ ν : M) (f : Polynomial (Polynomial A)) :
    (sqEv z q μ ν f).fst = ev2 z q f := by
  have : (fstHom S S M).toRingHom.comp (sqEv z q μ ν) = ev2 (A := A) z q := by
    apply Polynomial.ringHom_ext
    · intro g
      simp [sqEv_C, ev2]
    · simp [sqEv_X, ev2]
  exact congrArg (fun φ => φ f) this

theorem pow_inl_add_inr (a : S) (m : M) (N : ℕ) :
    (inl a + inr m : TrivSqZeroExt S M) ^ N = inl (a ^ N) + inr (((N : S) * a ^ (N - 1)) • m) := by
  have := eval_add_of_sq_eq_zero (X ^ N : Polynomial (TrivSqZeroExt S M)) (inl a) (inr m) (sq_inr m)
  simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_natCast] at this
  rw [this, eval_C, inl_pow, inl_pow, ← inl_natCast, ← inl_mul, inl_mul_inr]

end Gen
end LevDer
end GlobalTheory.AlmostEt

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

section Gen2
variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]
  [Module Sᵐᵒᵖ M] [IsCentralScalar S M]

theorem exists_evalBivariatePolynomialAt_of_mem_adjoin (z q : S) {x : S} (hx : x ∈ Algebra.adjoin A {z, q}) :
    ∃ f : Polynomial (Polynomial A), ev2 z q f = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨C X, by simp [ev2]⟩
    · exact ⟨X, by simp [ev2]⟩
  | algebraMap a => exact ⟨C (C a), by simp [ev2]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f + g, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f * g, map_mul _ _ _⟩

theorem exists_der_gen (z q : S) (μ ν : M)
    (hwd : ∀ f : Polynomial (Polynomial A), ev2 z q f = 0 → sqEv z q μ ν f = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin A {z, q}) D ∧ D z = μ ∧ D q = ν := by
  classical
  let D : S → M := fun x => (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) x)).snd
  have key : ∀ f : Polynomial (Polynomial A), D (ev2 z q f) = (sqEv z q μ ν f).snd := by
    intro f
    have h1 : ev2 z q (Function.invFun (ev2 (A := A) z q) (ev2 z q f)) = ev2 z q f :=
      Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun (ev2 (A := A) z q) (ev2 z q f) - f) (by rw [map_sub, h1, sub_self])
    rw [map_sub, sub_eq_zero] at h2
    show (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) (ev2 z q f))).snd = _
    rw [h2]
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx
    obtain ⟨g, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy
    rw [← map_add, key, key, key, map_add, snd_add]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx
    obtain ⟨g, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy
    rw [← map_mul, key, key, key, map_mul, snd_mul, op_smul_eq_smul, fst_sqEv, fst_sqEv]
  · intro a
    have : algebraMap A S a = ev2 z q (C (C a)) := by simp [ev2]
    rw [this, key, sqEv_C]
    simp
  · have : z = ev2 (A := A) z q (C X) := by simp [ev2]
    rw [this, key, sqEv_C]
    simp
  · have : q = ev2 (A := A) z q X := by simp [ev2]
    rw [this, key, sqEv_X]
    simp

end Gen2
end LevDer
end GlobalTheory.AlmostEt

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev ev (T : Tower p Ω) (n : ℕ) :
    Polynomial (Polynomial (O0 p)) →+* integralClosure (O0 p) Ω :=
  ev2 (zS T n) (qS T n)

theorem zS_prim (T : Tower p Ω) (n : ℕ) : IsPrimitiveRoot (zS T n) (p ^ n) :=
  IsPrimitiveRoot.of_map_of_injective (f := (integralClosure (O0 p) Ω).val.toRingHom)
    (T.prim n) Subtype.val_injective

theorem qS_pow (T : Tower p Ω) (n : ℕ) :
    qS T n ^ p ^ n = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact GlobalTheory.AlmostEt.qq_pow T n)

theorem aeval_cyc (T : Tower p Ω) (n : ℕ) :
    eval₂ (algebraMap (O0 p) (integralClosure (O0 p) Ω)) (zS T n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have := (zS_prim T n).isRoot_cyclotomic hpos
  rw [eval₂_eq_eval_map, map_cyclotomic]
  exact this

theorem le_ker_ev (T : Tower p Ω) (n : ℕ) : towerIdeal p n ≤ RingHom.ker (ev T n) := by
  rw [towerIdeal, Ideal.span_le]
  rintro b (rfl | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_C]
    exact aeval_cyc T n
  · simp only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_sub, eval₂_X_pow,
      eval₂_C, qS_pow, sub_self]

def kap (T : Tower p Ω) (n : ℕ) : On p n →+* integralClosure (O0 p) Ω :=
  Ideal.Quotient.lift _ (ev T n) (le_ker_ev T n)

theorem kap_mk (T : Tower p Ω) (n : ℕ) (f : Polynomial (Polynomial (O0 p))) :
    kap T n (Ideal.Quotient.mk _ f) = ev T n f := rfl

theorem kap_eq (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (a : On p n) :
    (kap T n a : Ω) = ι a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : ∀ c, ι (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) Ω c :=
    fun c => ι.commutes c
  have h2 : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) = T.ζ n := hι.1
  have h3 : ι (Ideal.Quotient.mk (towerIdeal p n) X) = T.qq n := hι.2
  have : ((integralClosure (O0 p) Ω).val.toRingHom.comp (ev T n)) =
      (ι.toRingHom.comp (Ideal.Quotient.mk (towerIdeal p n))) := by
    apply Polynomial.ringHom_ext
    · intro g
      induction g using Polynomial.induction_on' with
      | add g h hg hh => rw [C_add, map_add, map_add, hg, hh]
      | monomial k c =>
        rw [← C_mul_X_pow_eq_monomial, C_mul, C_pow]
        simp only [RingHom.coe_comp, Function.comp_apply, map_mul, map_pow, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, h1, h2]
        simp only [ev, ev2, coe_eval₂RingHom, eval₂_C, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]
        rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3]
      simp only [ev, ev2, coe_eval₂RingHom, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]
      rfl
  exact congrArg (fun φ => φ f) this

set_option synthInstance.maxHeartbeats 400000 in
theorem le_ker_sqEv (T : Tower p Ω) (n : ℕ) {M : Type} [AddCommGroup M]
    [Module (integralClosure (O0 p) Ω) M] [Module (integralClosure (O0 p) Ω)ᵐᵒᵖ M]
    [IsCentralScalar (integralClosure (O0 p) Ω) M] (μ ν : M)
    (hμ : (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0)
    (hν : ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0) :
    towerIdeal p n ≤ RingHom.ker (sqEv (A := O0 p) (zS T n) (qS T n) μ ν) := by
  rw [towerIdeal, Ideal.span_le]
  rintro b (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, sqEv_C, aeval_cyc, ← aeval_def, hμ, inl_zero, inr_zero,
      add_zero]
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, sqEv_X, sqEv_C, pow_inl_add_inr,
      Nat.cast_pow, hν, qS_pow]
    simp

end LevDer
end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

theorem exists_derOn_levelAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  intro p _ Ω _ _ hc T n hn M _ _ μ ν hμ hν
  letI : Module (integralClosure (O0 p) Ω)ᵐᵒᵖ M :=
    Module.compHom _ ((RingHom.id _).fromOpposite fun _ _ => mul_comm _ _)
  haveI : IsCentralScalar (integralClosure (O0 p) Ω) M := ⟨fun _ _ => rfl⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T n
  have hinj := GlobalTheory.T.tower_embedding_injective p Ω hc T n hn ι hι
  have hk : Function.Injective (kap T n) := by
    intro a b hab
    apply hinj
    rw [← kap_eq T n ι hι, ← kap_eq T n ι hι, hab]
  refine exists_der_gen (A := O0 p) (zS T n) (qS T n) μ ν fun f hf => ?_
  have h0 : Ideal.Quotient.mk (towerIdeal p n) f = 0 := hk (by rw [kap_mk, map_zero]; exact hf)
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  exact le_ker_sqEv T n μ ν hμ hν h0

end LevDer
end GlobalTheory.AlmostEt
