import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem isIntegral_of_charpoly_intGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Monic → aeval u (Q.map e.symm.toRingHom) = 0 → ∀ y : GLw m w, y ∈ GlobalTheory.LFun.KGL w m → y.val.charpoly = Q → IsIntegral K.O u := by
  intro E _ _ _ _ w _ K e _ hint _ B m b u Q hQ hu y hy hcp
  obtain ⟨z, rfl⟩ := hy
  have hcoef : ∀ i, Valued.v (Q.coeff i) ≤ 1 := by
    intro i
    rw [← hcp]
    have hm : ((bc (n := Fin m) (Ov E w).subtype z : GL (Fin m) (w.adicCompletion E)) :
        Matrix (Fin m) (Fin m) (w.adicCompletion E)) =
        (RingHom.mapMatrix (Ov E w).subtype) (z : Matrix (Fin m) (Fin m) (Ov E w)) := rfl
    rw [hm, RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (z.val.charpoly.coeff i).2
  have hlift : Q.map e.symm.toRingHom ∈ Polynomial.lifts (algebraMap K.O K.E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    have := (hint (e.symm (Q.coeff i))).2 (by simpa using hcoef i)
    simpa using this
  obtain ⟨P, hPm, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hQ.map _)
  refine ⟨P, hPmon, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K.E, hPm]
  exact hu

end GlobalTheory.TwLat
