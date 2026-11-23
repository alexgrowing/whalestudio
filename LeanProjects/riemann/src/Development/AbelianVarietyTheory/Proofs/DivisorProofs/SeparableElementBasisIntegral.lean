import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMulEqZeroImp
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.GramUnit

theorem isReduced_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (P : F[X]) (hP : P.Separable) (hu : aeval u P = 0) (hadj : Algebra.adjoin F {u} = ⊤) :
    IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨N, hN⟩ := hx
  have hxmem : x ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have hdvdP : minpoly F u ∣ P := minpoly.dvd F u hu
  have hsq : Squarefree (minpoly F u) := (hP.of_dvd hdvdP).squarefree
  have hfN : minpoly F u ∣ f ^ N := minpoly.dvd F u (by rw [map_pow]; exact hN)
  obtain ⟨g, hg⟩ := hsq.isRadical N f hfN
  subst hg
  change aeval u (minpoly F u * g) = 0
  rw [map_mul, minpoly.aeval, zero_mul]

theorem eq_zero_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    [IsReduced A] (x : A) (h : ∀ z, Algebra.trace F A (x * z) = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7; revert F A h_2 h_3 h_4 h_5 h_6 h_7 x h; exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp)
  | exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | (apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp ..)

theorem det_gram_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) [IsReduced B.A] {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (hβ : IsUnit β) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set y := ∑ i, v i • b i with hy
  have hlin : ∀ z, B.herm β y z = ∑ i, v i * B.herm β (b i) z := by
    intro z
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, hy, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hj : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    rw [hlin]
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct] using this
  have hsemi : ∀ (d : K.E) (a : B.A), B.σ (d • a) = K.c d • B.σ a := by
    intro d a
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hall : ∀ z, Algebra.trace K.E B.A (β * y * z) = 0 := by
    intro z
    have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
      rw [map_sum]
      simp only [hsemi]
    rw [hz, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    have := hj j
    simp only [GlobalTheory.UnitLemma.InvAlg.herm] at this
    rw [this, mul_zero]
  have hβy : β * y = 0 := eq_zero_of_trace_mul (β * y) hall
  have hy0 : y = 0 := by
    obtain ⟨u, rfl⟩ := hβ
    have := congrArg (fun t => ((u⁻¹ : B.Aˣ) : B.A) * t) hβy
    simpa [← mul_assoc] using this
  exact hv0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hy0))

end GlobalTheory.TwLat.GramUnit

open GlobalTheory.TwLat.GramUnit in

theorem GlobalTheory.TwLat.isUnit_gram_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b u P hP hu hadj β hβ
  haveI : IsReduced B.A := isReduced_of_adjoin u P hP hu hadj
  have hd := det_gram_ne_zero B b β hβ
  have hmap : GlobalTheory.TwLat.gram e b β = (Matrix.of fun i j => B.herm β (b i) (b j)).map e := by
    ext i j; rfl
  rw [hmap, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := RingHom.map_det (e : K.E →+* w.adicCompletion E) (Matrix.of fun i j => B.herm β (b i) (b j))
  rw [show ((Matrix.of fun i j => B.herm β (b i) (b j)).map e) =
    (e : K.E →+* w.adicCompletion E).mapMatrix (Matrix.of fun i j => B.herm β (b i) (b j)) from rfl, ← this]
  exact (map_ne_zero_iff _ e.injective).mpr hd
