import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdealStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem scaleRoots_derivative_eval₂_mul {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (P : Polynomial W)
    (s : W) (t : R) :
    c s * Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) =
      c s ^ P.natDegree * Polynomial.eval₂ c t (Polynomial.derivative P) := by
  have h : (P.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ P.natDegree * P := by
    have h0 := Polynomial.scaleRoots_eval₂_mul (p := P) (Polynomial.C : W →+* Polynomial W) Polynomial.X s
    rw [Polynomial.eval₂_C_X] at h0
    exact h0
  have h1 := congrArg (fun r => Polynomial.eval₂ c t (Polynomial.derivative r)) h
  simp only [Polynomial.derivative_comp, ← Polynomial.C_pow, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp, Polynomial.eval₂_X] at h1
  rw [h1, map_pow]

theorem exists_mul_derivative_scaleRoots_sub_mem {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (I : Ideal R)
    (P a b : Polynomial W) (s z : W) (hab : a * P + b * Polynomial.derivative P = Polynomial.C z) (t x : R)
    (ht : Polynomial.eval₂ c t P ∈ I) (hx : x - c s * t ∈ I) :
    ∃ b' : R, b' * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x - c s ^ P.natDegree * c z ∈ I := by
  refine ⟨Polynomial.eval₂ c t b * c s, ?_⟩
  obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub x (c s * t) (Polynomial.derivative ((P.scaleRoots s).map c))
  have h1 := scaleRoots_derivative_eval₂_mul c P s t
  have h2 := congrArg (Polynomial.eval₂ c t) hab
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h2
  have h3 : (Polynomial.derivative ((P.scaleRoots s).map c)).eval (c s * t) =
      Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
  rw [h3] at hw
  have h4 : Polynomial.eval₂ c t b * c s * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x -
      c s ^ P.natDegree * c z = (Polynomial.eval₂ c t b * c s * w) * (x - c s * t) -
        (c s ^ P.natDegree * Polynomial.eval₂ c t a) * Polynomial.eval₂ c t P := by
    linear_combination (Polynomial.eval₂ c t b * c s) * hw + Polynomial.eval₂ c t b * h1 +
      c s ^ P.natDegree * h2
  rw [h4]
  exact I.sub_mem (I.mul_mem_left _ hx) (I.mul_mem_left _ ht)

theorem eval₂_C_X_powerSeries {W : Type} [CommRing W] (P : Polynomial W) :
    Polynomial.eval₂ (PowerSeries.C : W →+* W⟦X⟧) X P = (P : W⟦X⟧) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, hp, hq, Polynomial.coe_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X]

theorem approxRoot_image_indep_general_rings {W R : Type} [CommRing W] [CommRing R] (l n m c : ℕ) (P a b : Polynomial W)
    (hab : a * P + b * Polynomial.derivative P = Polynomial.C ((l : W) ^ c)) (q : W⟦X⟧)
    (h1 : (P : W⟦X⟧) ∣ q - (l : W⟦X⟧) ^ m * X)
    (h2 : (P : W⟦X⟧) ^ n ∣ Polynomial.eval₂ PowerSeries.C q (P.scaleRoots ((l : W) ^ m)))
    (I : Ideal R) (f g : W⟦X⟧ →+* R) (hC : ∀ w, f (PowerSeries.C w) = g (PowerSeries.C w)) (hX : f X - g X ∈ I)
    (hI : I = Ideal.span {f P}) (hI' : I = Ideal.span {g P}) :
    ∃ k : ℕ, f P ^ n ∣ (l : R) ^ k * (f q - g q) := by
  have hfE : f P ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hgE : g P ∈ I := by rw [hI']; exact Ideal.mem_span_singleton_self _
  have hcomp : f.comp PowerSeries.C = g.comp PowerSeries.C := RingHom.ext hC
  have hroot : ∀ h : W⟦X⟧ →+* R, h P ∈ I →
      ((P.scaleRoots ((l : W) ^ m)).map (h.comp PowerSeries.C)).eval (h q) ∈ I ^ n := by
    intro h hE
    obtain ⟨y, hy⟩ := h2
    rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hy, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hE n)
  have hcong : ∀ h : W⟦X⟧ →+* R, h P ∈ I → h q - (l : R) ^ m * h X ∈ I := by
    intro h hE
    obtain ⟨y, hy⟩ := h1
    have := congrArg h hy
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ hE
  have hxy : f q - g q ∈ I := by
    have : f q - g q = (f q - (l : R) ^ m * f X) - (g q - (l : R) ^ m * g X) + (l : R) ^ m * (f X - g X) := by ring
    rw [this]
    exact I.add_mem (I.sub_mem (hcong f hfE) (hcong g hgE)) (I.mul_mem_left _ hX)
  obtain ⟨b', hb'⟩ := exists_mul_derivative_scaleRoots_sub_mem (f.comp PowerSeries.C) I P a b
    ((l : W) ^ m) _ hab (f X) (f q)
    (by rw [← Polynomial.hom_eval₂, eval₂_C_X_powerSeries]; exact hfE)
    (by rw [map_pow, map_natCast]; exact hcong f hfE)
  have hg := hroot g hgE
  rw [← hcomp] at hg
  have key := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I _ _ _ _ _ n (hroot f hfE) hg hxy hb'
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow, map_pow, map_natCast, ← pow_mul, ← pow_add,
    ← pow_mul] at key
  exact ⟨_, key⟩

theorem approx_root_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  intro l _ K bk n m q h1 h2 B f g
  obtain ⟨hC, hX, hI⟩ := GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g
  obtain ⟨-, -, hI'⟩ := GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B g f
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I (BK.hf f) (BK.hf g) hC hX hI hI'

end GlobalTheory.BSP
