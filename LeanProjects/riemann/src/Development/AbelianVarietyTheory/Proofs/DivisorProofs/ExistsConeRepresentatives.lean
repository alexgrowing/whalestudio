import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallCTReps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul (a : UA σ J) : mat a⁻¹ * mat a = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

def Rel (v : Fin n → AE F E) (a b : UA σ J) : Prop := ∃ l : (AE F E)ˣ, mat (a * b⁻¹) *ᵥ v = l.1 • v

theorem rel_refl (v : Fin n → AE F E) (a : UA σ J) : Rel v a a :=
  ⟨1, by rw [mul_inv_cancel, mat_one, Matrix.one_mulVec, Units.val_one, one_smul]⟩

theorem rel_symm (v : Fin n → AE F E) {a b : UA σ J} (h : Rel v a b) : Rel v b a := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l⁻¹, ?_⟩
  have hi : b * a⁻¹ = (a * b⁻¹)⁻¹ := by group
  have key : mat (b * a⁻¹) *ᵥ (mat (a * b⁻¹) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hi, mat_inv_mul, Matrix.one_mulVec]
  rw [hl, Matrix.mulVec_smul] at key
  calc mat (b * a⁻¹) *ᵥ v = (l⁻¹).1 • (l.1 • mat (b * a⁻¹) *ᵥ v) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • v := by rw [key]

theorem rel_trans (v : Fin n → AE F E) {a b c : UA σ J} (h₁ : Rel v a b) (h₂ : Rel v b c) : Rel v a c := by
  obtain ⟨l, hl⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  refine ⟨l * m, ?_⟩
  have hs : a * c⁻¹ = (a * b⁻¹) * (b * c⁻¹) := by group
  rw [hs, mat_mul, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, hl, smul_smul, Units.val_mul, mul_comm]

def setoidRat (v : Fin n → AE F E) : Setoid (ratU σ J) where
  r a b := Rel v a.1 b.1
  iseqv := ⟨fun a => rel_refl v a.1, fun h => rel_symm v h, fun h₁ h₂ => rel_trans v h₁ h₂⟩

end GlobalTheory.ConeSmallCTReps

open GlobalTheory.ConeSmallCTReps in

theorem GlobalTheory.ConeSmallCT.exists_isReps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E), ∃ T : Set (UA σ J), GlobalTheory.ConeSmallCT.IsReps T x := by
  intro F E _ _ _ _ _ σ n J x
  let S := setoidRat (σ := σ) (J := J) (incV F x)
  refine ⟨Set.range (fun q : Quotient S => (q.out : UA σ J)), ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact q.out.2
  · intro γ hγ
    let g : ratU σ J := ⟨γ, hγ⟩
    refine ⟨((⟦g⟧ : Quotient S).out : UA σ J), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have h : S.r (⟦g⟧ : Quotient S).out g := Quotient.mk_out (s := S) g
      exact rel_symm _ h
    · rintro t ⟨⟨q, rfl⟩, ht⟩
      have h1 : S.r g q.out := ht
      have h2 : S.r q.out (⟦g⟧ : Quotient S).out := rel_trans _ (rel_symm _ h1) (rel_symm _ (Quotient.mk_out (s := S) g))
      have : q = ⟦g⟧ := Quotient.out_equiv_out.mp h2
      rw [this]
