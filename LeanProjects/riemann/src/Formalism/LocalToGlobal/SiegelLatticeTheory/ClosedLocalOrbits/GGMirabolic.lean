import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
import Formalism.HermitianCurvature.StatementPB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic

namespace Formalism.L2.SG.GGMirabolic

open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section One

variable {F : Type} [Field F] [Fintype F] (k : ℕ)

variable {k}

def psiNat (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : ℂ := if IsUni k x then psiU ψ₀ x else 0

variable (F k) in

def cardU : ℕ := Nat.card {x : GL (Fin k) F // IsUni k x}

def gam (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : ℂ :=
  ((cardU F k : ℂ))⁻¹ * ∑ y : GL (Fin k) F, psiNat ψ₀ (y * x * y⁻¹)

def repGam (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) : V →ₗ[ℂ] V :=
  ∑ x : GL (Fin k) F, gam ψ₀ x • π x

def Generic (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) : Prop :=
  ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ IsWhit ψ₀ π ℓ

theorem isUni_one : IsUni k (1 : GL (Fin k) F) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  simp [(ne_of_lt hij).symm]

theorem superdiag_one : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
  unfold superdiag
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := by intro e; subst e; omega
    simp [this]
  · rfl

theorem gam_one (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (Fintype.card (GL (Fin k) F) : ℂ) / (cardU F k : ℂ) := by
  have hp : ∀ y : GL (Fin k) F, psiNat ψ₀ (y * 1 * y⁻¹) = 1 := by
    intro y
    rw [mul_one, mul_inv_cancel]
    simp only [psiNat, isUni_one, if_true, psiU, Units.val_one, superdiag_one, AddChar.map_zero_eq_one]
  unfold gam
  rw [Finset.sum_congr rfl (fun y _ => hp y)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [div_eq_inv_mul]

end One

def MirabolicBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → Generic ψ₀ π →
      ∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) ≤ Module.finrank ℂ V

def CardUni : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), cardU F k = Fintype.card F ^ (k * (k - 1) / 2)

def ConvScalar : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      (gam ψ₀ (1 : GL (Fin k) F))⁻¹ • repGam ψ₀ π =
        if Generic ψ₀ π then ((cardU F k : ℂ) / (Module.finrank ℂ V : ℂ)) • LinearMap.id else 0

def ConvScalarOfLit : Prop := GelfandGraevMultOne → ConvScalar

def GenericRatio : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → Generic ψ₀ π →
      (cardU F k : ℝ) / (Module.finrank ℂ V : ℝ) ≤
        ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹

def GenericRatioOfBound : Prop := MirabolicBound → CardUni → GenericRatio

theorem ratio_numeric (k : ℕ) (q : ℝ) (hq : 3 ≤ q) :
    ∏ i ∈ Finset.Ico 1 k, (1 - (q ^ i)⁻¹)⁻¹ ≤ 1 + 3 / q := by
  have h := Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_GGNumeric (k - 1) q hq
  have he : Finset.Ico 1 k = Finset.Icc 1 (k - 1) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [he]; exact h

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

def gamProd (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ := ∏ v, gam (ψ v) (x v)

end Prod

def GGMatrixBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ), (∀ v, ψ v ≠ 1) → (∀ v, 3 ≤ Fintype.card (Fq v)) →
    ∀ (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
      (∀ (x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ) (j : X), x • j = j → x = 1) →
      ∀ d : X → X → (∀ v, GL (Fin k) (Fq v)),
        (∀ i j, (∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) →
        (Matrix.of fun i j =>
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then gamProd ψ (d i j) else 0).PosSemidef ∧
        ((((∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ))) *
            (gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v))).re : ℝ) : ℂ) • (1 : Matrix X X ℂ) -
          Matrix.of fun i j =>
            if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0).PosSemidef

def GGMatrixBoundOfLit : Prop := GelfandGraevMultOne → MirabolicBound → GGMatrixBound

def TermsGGBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ), (∀ v, ψ v ≠ 1) → (∀ v, 3 ≤ Fintype.card (Fq v)) →
    ∀ (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
      (∀ (x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ) (j : X), x • j = j → x = 1) →
      ∀ d : X → X → (∀ v, GL (Fin k) (Fq v)),
        (∀ i j, (∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) →
      ∀ (τ Rw H H₁ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw X H H₁),
        (∀ i j, T.GG i j =
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0) →
        T.Gam1 = (gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v))).re →
        T.GGBound (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ)))

theorem termsGGBound_of_matrix (h : GGMatrixBound) : TermsGGBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd τ Rw H H₁ _ _ _ _ T hGG hG1
  have h2 := (h ι Fq k ψ hψ hq X hfree d hd).2
  unfold Formalism.FourierDecayAlt.PB.Terms.GGBound
  have hM : Matrix.of T.GG = Matrix.of fun i j =>
      if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0 := by
    ext i j; simp [hGG]
  rw [hM, hG1]
  convert h2 using 3

end

end Formalism.L2.SG.GGMirabolic
