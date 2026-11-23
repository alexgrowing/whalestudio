import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.InertTens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] {m n : ℕ} (P : Matrix (Fin m) (Fin n) L) (J : Matrix (Fin m) (Fin m) L)
    (K : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin m) (Fin n) L) :
    ∑ i, ∑ j, ∑ k, ∑ l, P i j * J i k * K j l * Q k l = (Pᵀ * J * Q * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem trace_orth {L : Type} [Field L] (σL : L →+* L) {m n : ℕ} (J : Matrix (Fin m) (Fin m) L) (K : Matrix (Fin n) (Fin n) L)
    (A : Matrix (Fin m) (Fin m) L) (Bm : Matrix (Fin n) (Fin n) L) (δ : L)
    (hA : Aᵀ * J * A.map σL = 1) (hB : Bmᵀ * K * Bm.map σL = δ • 1) (x y : Matrix (Fin n) (Fin m) L) :
    ((A * xᵀ * Bmᵀ)ᵀ * J * (A * yᵀ * Bmᵀ).map σL * Kᵀ).trace = δ * ((y.map σL)ᵀ * x).trace := by
  have e1 : (A * yᵀ * Bmᵀ).map σL = A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
  have e2 : (Bm.map σL)ᵀ * Kᵀ * Bm = δ • 1 := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : Bm * (x * Aᵀ) * J * (A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ) * Kᵀ
      = Bm * (x * (Aᵀ * J * A.map σL) * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ)) := by
    simp only [Matrix.mul_assoc]
  rw [e3, hA, Matrix.trace_mul_comm, Matrix.mul_one]
  have e4 : x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ) * Bm = x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ * Bm) := by
    simp only [Matrix.mul_assoc]
  rw [e4, e2, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hTens_kap (σ : E →ₐ[F] E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {σL : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h σL)
    {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x y : Matrix (Fin n) (Fin m) (w.adicCompletion E)) :
    hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
      ptAt hw h (∑ i, ∑ j, ∑ k, ∑ l, (A * xᵀ * Bmᵀ) i j * JA.map (algebraMap E (w.adicCompletion E)) i k *
        JB.map (algebraMap E (w.adicCompletion E)) j l * (A * yᵀ * Bmᵀ).map σL k l) := by
  have hr : ∀ (a : E) (z : w.adicCompletion E),
      ptAt hw h z * inclR (F := F) (AF F) a = ptAt hw h (z * algebraMap E (w.adicCompletion E) a) := by
    intro a z
    rw [mul_comm, inclR_mul_ptAt, mul_comm]
  simp only [hTens, incM, kap_apply, Matrix.map_apply, cA_ptAt hw h σ hc, hr, ← map_mul, map_sum]

end GlobalTheory.InertTens

namespace GlobalTheory.InertTens

theorem hTens_kap_eq_locH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc m n JA JB A Bm δ hA hB x y
  rw [hTens_kap σ hw h hc, quadruple_sum_eq_trace_transpose_mul, trace_orth σL _ _ A Bm δ hA hB x y]
  congr 1
  simp [GlobalTheory.Hk3.locH]

end GlobalTheory.InertTens
