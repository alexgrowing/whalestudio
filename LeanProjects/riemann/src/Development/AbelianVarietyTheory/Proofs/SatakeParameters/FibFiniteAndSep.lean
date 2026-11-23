import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibFin

variable (k : Type) [Field k] {F : Type} (K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

abbrev coordIdeal : Ideal (rB k K x {0}) :=
  Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))

def incl : rA k x {0} →ₐ[k] rB k K x {0} where
  toFun a := ⟨algebraMap F K a, (integralClosure (rA k x {0}) K).algebraMap_mem a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp [← IsScalarTower.algebraMap_apply]

theorem coe_incl (a : rA k x {0}) : (incl k K x a : K) = algebraMap F K a := rfl

theorem mk_incl (hpd : IsPd k x) : ∃ ε : rA k x {0} →ₐ[k] k,
    (Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x) = (Algebra.ofId k _).comp ε := by
  obtain ⟨e, he⟩ := GlobalTheory.PD.rA_single_polyEquiv k F d x hpd 0
  refine ⟨(MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom, ?_⟩
  have key : ((Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x)).comp e.toAlgHom =
      ((Algebra.ofId k _).comp ((MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom)).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : incl k K x (e (MvPolynomial.X j)) = (⟨_, tco_mem k K x j⟩ : rB k K x {0}) := by
      apply Subtype.ext
      rw [coe_incl, he j, Fin.succAbove_zero]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk _ (incl k K x (e (MvPolynomial.X j))) =
      Algebra.ofId k _ (MvPolynomial.aeval (0 : Fin d → k) (e.symm (e (MvPolynomial.X j))))
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X, Pi.zero_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
  ext a
  have := congrArg (fun φ : MvPolynomial (Fin d) k →ₐ[k] _ => φ (e.symm a)) key
  simpa using this

theorem finite_quot (h : IsFinCover k K x) : Module.Finite k (rB k K x {0} ⧸ coordIdeal k K x) := by
  haveI := h.smooth 0
  haveI : Algebra.FiniteType k (rB k K x {0} ⧸ coordIdeal k K x) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨ε, hε⟩ := mk_incl k K x h.pd
  have hε' : (algebraMap k (rB k K x {0} ⧸ coordIdeal k K x)).comp ε.toRingHom =
      (Ideal.Quotient.mk (coordIdeal k K x)).comp (incl k K x).toRingHom :=
    RingHom.ext fun a => by simpa using (AlgHom.congr_fun hε a).symm
  have hcomp : (rB k K x {0}).val.toRingHom.comp (incl k K x).toRingHom = algebraMap (rA k x {0}) K :=
    RingHom.ext fun a => rfl
  haveI : Algebra.IsIntegral k (rB k K x {0} ⧸ coordIdeal k K x) := ⟨fun q => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA k x {0}) (b : K) := b.2
    have hq : Polynomial.eval₂ (incl k K x).toRingHom b p = 0 := by
      apply Subtype.ext
      change (rB k K x {0}).val.toRingHom (Polynomial.eval₂ (incl k K x).toRingHom b p) = (0 : K)
      rw [Polynomial.hom_eval₂, hcomp]
      exact hp
    refine ⟨p.map ε.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hε', ← Polynomial.hom_eval₂, hq, map_zero]⟩
  exact Algebra.IsIntegral.finite

theorem fib_finite_and_sep [IsAlgClosed k] (h : IsFinCover k K x)
    (hred : IsReduced (rB k K x {0} ⧸ coordIdeal k K x)) :
    Finite (fib k K x) ∧ ∀ f : rB k K x {0}, (∀ e : fib k K x, e.1 f = 0) → f ∈ coordIdeal k K x := by
  haveI := finite_quot k K x h
  have hker : ∀ e : fib k K x, coordIdeal k K x ≤ RingHom.ker e.1 := fun e => by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact e.2 j
  let L : fib k K x → (rB k K x {0} ⧸ coordIdeal k K x →ₐ[k] k) := fun e =>
    Ideal.Quotient.liftₐ _ e.1 (fun a ha => hker e ha)
  have hL : ∀ e f, L e (Ideal.Quotient.mk _ f) = e.1 f := fun e f => rfl
  refine ⟨Finite.of_injective L fun e₁ e₂ he => Subtype.ext (AlgHom.ext fun f => by rw [← hL, ← hL, he]),
    fun f hf => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsArtinianRing (rB k K x {0} ⧸ coordIdeal k K x) := IsArtinianRing.of_finite k _
  have hmem : Ideal.Quotient.mk (coordIdeal k K x) f ∈ Ideal.jacobson (⊥ : Ideal (rB k K x {0} ⧸ coordIdeal k K x)) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    haveI := hm.isPrime
    haveI : Module.Finite k (_ ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
    haveI : Algebra.IsIntegral k (_ ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij : Function.Bijective (algebraMap k (_ ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let ψ := (AlgEquiv.ofBijective (Algebra.ofId k (_ ⧸ m)) hbij).symm
    let χ := (ψ.toAlgHom.comp (Ideal.Quotient.mkₐ k m)).comp (Ideal.Quotient.mkₐ k (coordIdeal k K x))
    have hχ : ∀ j : Fin d, χ ⟨_, tco_mem k K x j⟩ = 0 := fun j => by
      have hz : Ideal.Quotient.mkₐ k (coordIdeal k K x) ⟨_, tco_mem k K x j⟩ = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2
          (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
      simp only [χ, AlgHom.comp_apply, hz, map_zero]
    have h0 : ψ (Ideal.Quotient.mk m (Ideal.Quotient.mk (coordIdeal k K x) f)) = 0 := hf ⟨χ, hχ⟩
    rw [map_eq_zero_iff _ ψ.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := rB k K x {0} ⧸ coordIdeal k K x)
  have hpow : (Ideal.Quotient.mk (coordIdeal k K x) f) ^ n = 0 := by
    have := Ideal.pow_mem_pow hmem n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  exact IsNilpotent.eq_zero ⟨n, hpow⟩

end GlobalTheory.PD.FibFin
