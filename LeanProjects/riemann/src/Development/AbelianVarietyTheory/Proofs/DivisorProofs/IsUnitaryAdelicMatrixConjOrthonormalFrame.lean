import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem sg_one_tmul (c : E ≃ₐ[F] E) (e : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c e := by
  simp [sg, Algebra.TensorProduct.map_tmul]

theorem fm_map_sg (c : E ≃ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) :
    (fm F A).map (sg (FiniteAdeleRing (𝓞 F) F) c) = fm F (A.map c) := by
  ext i j
  simp only [fm, Matrix.map_apply, sg_one_tmul]

theorem hermA_eq_dot (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c H x y = x ⬝ᵥ (fm F H *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  simp only [hermA, dotProduct, Matrix.mulVec, fm, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermA_mulVec (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (RA F E))
    (x y : Fin n → RA F E) :
    hermA c H (M *ᵥ x) (M *ᵥ y) =
      x ⬝ᵥ ((Mᵀ * fm F H * M.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  rw [hermA_eq_dot]
  have h1 : (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((M *ᵥ y) b)) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b) := by
    funext b
    exact RingHom.map_mulVec (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom M y b
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sg_single (c : E ≃ₐ[F] E) (j : Fin n) :
    (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((Pi.single j (1 : RA F E) : Fin n → RA F E) b)) = Pi.single j 1 := by
  funext b
  by_cases h : b = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem mat_eq_of_dot (c : E ≃ₐ[F] E) {K K' : Matrix (Fin n) (Fin n) (RA F E)}
    (h : ∀ x y : Fin n → RA F E, x ⬝ᵥ (K *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) =
      x ⬝ᵥ (K' *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b))) : K = K' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [sg_single] at this
  simpa [Matrix.mulVec_single_one] using this

theorem gram_of_isUnA (c : E ≃ₐ[F] E) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    gᵀ * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = 1 := by
  have h := mat_eq_of_dot c (K := gᵀ * fm F 1 * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) (K' := fm F 1)
    fun x y => by rw [← hermA_mulVec, ← hermA_eq_dot]; exact hg x y
  rwa [GlobalTheory.UnRep.FullReps.fm_one, Matrix.mul_one] at h

end General

end GlobalTheory.UnitConjFrame

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem map_mul_sg (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) (RA F E)) :
    (M * N).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) * N.map (sg (FiniteAdeleRing (𝓞 F) F) c) :=
  Matrix.map_mul (f := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom)

theorem map_mul_c (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) E) :
    (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : E →+* E))

theorem fm_transpose (A : Matrix (Fin n) (Fin n) E) : (fm F A)ᵀ = fm F Aᵀ := by
  ext i j; rfl

theorem isUnA_conj (c : E ≃ₐ[F] E) (A B G : Matrix (Fin n) (Fin n) E) (hAB : A * B = 1)
    (h : Aᵀ * Gᵀ * A.map c = 1) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    IsUnA c Gᵀ (fm F A * g * fm F B) := by
  have hg' := gram_of_isUnA c hg
  have hB : Bᵀ * B.map c = Gᵀ := by
    have e1 : Bᵀ * B.map c = Bᵀ * (Aᵀ * Gᵀ * A.map c) * B.map c := by rw [h, Matrix.mul_one]
    rw [e1, ← Matrix.transpose_transpose Gᵀ]
    have e2 : (A * B).map c = A.map c * B.map c := map_mul_c c A B
    rw [hAB, Matrix.map_one _ (map_zero c) (map_one c)] at e2
    calc Bᵀ * (Aᵀ * Gᵀᵀᵀ * A.map c) * B.map c = (A * B)ᵀ * Gᵀᵀᵀ * (A.map c * B.map c) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Gᵀᵀᵀ := by rw [hAB, ← e2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : (fm F A * g * fm F B)ᵀ * fm F Gᵀ * (fm F A * g * fm F B).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      fm F Gᵀ := by
    rw [map_mul_sg, map_mul_sg, fm_map_sg, fm_map_sg, Matrix.transpose_mul, Matrix.transpose_mul,
      fm_transpose, fm_transpose]
    have e3 : fm F Aᵀ * fm F Gᵀ * fm F (A.map c) = 1 := by
      rw [← GlobalTheory.UnRep.FullReps.fm_mul, ← GlobalTheory.UnRep.FullReps.fm_mul, h, GlobalTheory.UnRep.FullReps.fm_one]
    calc _ = fm F Bᵀ * (gᵀ * (fm F Aᵀ * fm F Gᵀ * fm F (A.map c)) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *
            fm F (B.map c) := by simp only [Matrix.mul_assoc]
      _ = fm F Gᵀ := by
          rw [e3, Matrix.mul_one, hg', Matrix.mul_one, ← GlobalTheory.UnRep.FullReps.fm_mul, hB]
  intro x y
  rw [hermA_mulVec, hM, hermA_eq_dot]

end General

end GlobalTheory.UnitConjFrame

theorem GlobalTheory.UnitConjFrame.isUnA_frame_conj : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  intro D V fr g hfr hg
  refine GlobalTheory.UnitConjFrame.isUnA_conj (GlobalTheory.Member.cF D) fr.1 (fr⁻¹).1 V.gram (Units.mul_inv fr) ?_ hg
  have h := congrArg Matrix.transpose hfr
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  rw [← h, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.mul_assoc]
  rfl
