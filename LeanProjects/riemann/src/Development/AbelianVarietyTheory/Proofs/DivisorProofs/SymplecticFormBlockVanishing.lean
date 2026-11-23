import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.SympVan

theorem hTens_mul_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β μ : Type} [Fintype α] [Fintype β] [Fintype μ] (JA : Matrix α α A) (JB : Matrix β β A)
    (P : Matrix α μ A) (w : Matrix μ β A) (a : A) (u : α → A) (v : β → A)
    (h : (fun i => ∑ k, JA i k * c (u k)) ᵥ* P = 0) :
    hTens c JA JB (P * w) (a • Matrix.vecMulVec u v) = 0 := by
  have h2 : ∀ j, ∑ i, (P * w) i j * (∑ k, JA i k * c (u k)) = 0 := by
    intro j
    have := congrFun (Matrix.vecMul_vecMul (fun i => ∑ k, JA i k * c (u k)) P w) j
    rw [h, Matrix.zero_vecMul] at this
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this.symm
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have e : ∀ i, (∑ k, ∑ l, (P * w) i j * JA i k * JB j l * c ((a • Matrix.vecMulVec u v) k l)) =
      (∑ k, (P * w) i j * (JA i k * c (u k))) * ∑ l, JB j l * c a * c (v l) := by
    intro i
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul]
    ring
  simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, h2, zero_mul]

end GlobalTheory.ThK.SympVan

open GlobalTheory.ThK.SympVan in

theorem GlobalTheory.ThK.symp_shiftA_vanish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    CfgA B G G₁ H H' → ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)) (l : (AE F E)ˣ),
      symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ) (shiftA H H' l) = 0 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC z l
  unfold symp
  rw [Matrix.mul_assoc, shiftA, hTens_mul_vecMulVec, mul_zero, map_zero]
  ext m
  have h0 := ((hC.hH).orth (Pi.single m 1)).1
  have e : (fun i => ∑ k, incM F G.V.J i k * cA σ (incV F H.x k)) ᵥ* incM F H.ι =
      fun m => inclR (F := F) (AF F) (form σ G.V.J (H.ι *ᵥ Pi.single m 1) H.x) := by
    ext m
    have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
    simp only [Matrix.vecMul, dotProduct, incM, incV, Matrix.map_apply, hc, ← map_mul, ← map_sum]
    congr 1
    simp only [form, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e]; simp only [h0, map_zero, Pi.zero_apply]
