import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ratHerm_herm_unit_aniso : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K)
    (v0 : InfinitePlace K), IsConjAt v0 → ∀ (n j : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 G X →
    Gᴴ = G ∧ IsUnit G.det ∧ ∀ e : Fin j → Fin n → K, LinearIndependent K e → gramR G e ≠ 0 := by
  intro K _ _ _ K0 v0 hc n j G X hG
  set s0 : K →+* ℂ := v0.embedding with hs0
  obtain ⟨hXu, hXG⟩ := hG.2 v0
  set Y : Matrix (Fin n) (Fin n) ℂ := (X v0)⁻¹ with hY
  have hYu : IsUnit Y.det := Matrix.isUnit_nonsing_inv_det _ hXu
  have hYinj : Function.Injective Y.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hYu)
  have hpos : (G.map s0).PosDef := by
    rw [← hXG]; exact Matrix.PosDef.conjTranspose_mul_self _ hYinj
  have hstar : ∀ {m d : ℕ} (E : Matrix (Fin m) (Fin d) K), (Eᴴ).map s0 = (E.map s0)ᴴ :=
    fun E => Formalism.L2.DIV.map_conjTranspose' s0 E (fun i a => hc (E i a))
  have hmapinj : ∀ {m d : ℕ} {A B : Matrix (Fin m) (Fin d) K}, A.map s0 = B.map s0 → A = B := by
    intro m d A B h
    ext i k
    exact s0.injective (congrFun (congrFun h i) k)
  refine ⟨?_, ?_, ?_⟩
  · apply hmapinj
    rw [hstar, hpos.1.eq]
  · rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : s0 G.det = (G.map s0).det := RingHom.map_det s0 G
    rw [h0, map_zero] at h1
    exact hpos.det_pos.ne' h1.symm
  · intro e he
    set E : Matrix (Fin n) (Fin j) K := Matrix.of fun i b => e b i with hE
    have hEinj : Function.Injective E.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact he
    have hgram : (Matrix.of fun a b => star (e a) ⬝ᵥ G.mulVec (e b)) = Eᴴ * G * E := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hE, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hPD : ((E.map s0)ᴴ * G.map s0 * E.map s0).PosDef :=
      hpos.conjTranspose_mul_mul_same (Formalism.L2.DIV.map_inj s0 E hEinj)
    unfold gramR
    rw [hgram]
    intro h0
    have h1 : s0 (Eᴴ * G * E).det = ((Eᴴ * G * E).map s0).det := RingHom.map_det s0 _
    rw [h0, map_zero, Matrix.map_mul, Matrix.map_mul, hstar] at h1
    exact hPD.det_pos.ne' h1.symm

end GlobalTheory
