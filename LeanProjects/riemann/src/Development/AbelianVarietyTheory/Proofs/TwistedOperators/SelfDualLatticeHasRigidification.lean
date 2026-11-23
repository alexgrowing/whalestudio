import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.RigExists

theorem exists_cartan_onb {k p q : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (h : Formalism.UG.HasSignature G p q) :
    ∃ s B : Matrix (Fin k) (Fin k) ℂ, IsCartanInv G s ∧ IsONBasis G s B p := by
  obtain ⟨e, P, hP⟩ := h
  have hk : k = p + q := by simpa using Fintype.card_congr e
  subst hk
  set f : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm with hf
  set ε : Fin (p + q) → ℝ := fun a => if a.val < p then 1 else -1 with hε
  set B : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := (P : Matrix _ _ ℂ).submatrix e f with hB
  set A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).submatrix f e with hA
  set Dg : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := Matrix.diagonal fun a => (ε a : ℂ) with hDg
  have e1 : B * A = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ f.bijective, Units.mul_inv, Matrix.submatrix_one_equiv]
  have e2 : A * B = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_one_equiv]
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j; simp
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (P : Matrix _ _ ℂ)ᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT] at hP
  have hD : Bᴴ * G * B = Dg := by
    have : Bᴴ * G * B = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * G.reindex e e *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix f f := by
      rw [hB, Matrix.conjTranspose_submatrix, hG, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
        ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← hG]
    rw [this, hP]
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [Formalism.UG.Jpq, hf, hDg, hε, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> (try omega) <;> split_ifs <;> simp
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; simp only [hε]; split_ifs <;> simp
  have hDh : Dgᴴ = Dg := by
    rw [hDg, Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp [hε]
  have e3 : Bᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  have e4 : Aᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have hGA : G = Aᴴ * Dg * A := by
    rw [← hD]
    calc G = (Aᴴ * Bᴴ) * G * (B * A) := by rw [e4, e1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨B * Dg * A, B, ⟨?_, ?_, ?_⟩, ε, fun a => ?_, hD, ?_⟩
  · calc B * Dg * A * (B * Dg * A) = B * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one, e1]
  · conv_lhs => rw [hGA]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ Aᴴ, e3, Matrix.one_mul, ← Matrix.mul_assoc A B, e2, Matrix.one_mul,
      ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hGA, Matrix.mul_assoc]
  · have : G * (B * Dg * A) = Aᴴ * A := by
      rw [hGA]
      calc Aᴴ * Dg * A * (B * Dg * A) = Aᴴ * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
        _ = Aᴴ * A := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one]
    rw [this]
    exact Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e1)))
  · simp only [hε]; split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, not_lt.1 h⟩
  · calc B * Dg * A * B = B * Dg * (A * B) := by simp only [Matrix.mul_assoc]
      _ = B * Dg := by rw [e2, Matrix.mul_one]

theorem exists_rig : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  intro D V Λ hV hΛ
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hΛ.1
  have hτ : ∀ τ : D.what₂.Tau, ∃ s B : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      IsCartanInv (gramAt D V τ) s ∧ ∃ p, IsONBasis (gramAt D V τ) s B p := fun τ => by
    obtain ⟨s, B, h1, h2⟩ := exists_cartan_onb (gramAt D V τ) (hV (tauE D τ))
    exact ⟨s, B, h1, _, h2⟩
  choose s B hsB using hτ
  exact ⟨⟨Λ, β, s, B⟩, rfl, hΛ, hβ, hsB⟩

end GlobalTheory.RigExists
