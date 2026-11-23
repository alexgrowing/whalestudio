import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} (ι : K → Type) (J : Type)

def extIdx : Option K → Type := fun o => Option.elim o J ι

instance extIdx.instFintype [∀ k, Fintype (ι k)] [Fintype J] : ∀ o, Fintype (extIdx ι J o)
  | none => inferInstanceAs (Fintype J)
  | some k => inferInstanceAs (Fintype (ι k))

variable {ι J}

def liftForm {R : Type*} [CommRing R] : MRing ι R →ₐ[R] MRing (extIdx ι J) R :=
  rename fun v => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)

def newVar {R : Type*} [CommRing R] (j : J) : MRing (extIdx ι J) R :=
  X (⟨none, j⟩ : Σ o, extIdx ι J o)

def blowUpSubst {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (u : J → MRing ι R) :
    (Σ o, extIdx ι J o) → Polynomial (MRing ι R ⧸ P)
  | ⟨none, j⟩ => Polynomial.C (Ideal.Quotient.mk P (u j)) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (Ideal.Quotient.mk P (X ⟨k, i⟩))

def blowUpOf {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (u : J → MRing ι R) :
    Ideal (MRing (extIdx ι J) R) :=
  RingHom.ker (aeval (blowUpSubst P u))

end Objects

def liftMDeg {K : Type*} (c : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 c

def liftDegs {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) : Fin n → Option K → ℤ := fun i => liftDeg (L i)

abbrev BlowUpIdx {K : Type*} (ι : K → Type) : Type _ := Option (Option (∀ k, ι k))

section Gens

variable {K : Type*} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

def powMonomial (e : K → ℕ) (i : ∀ k, ι k) : MRing ι R := ∏ k, X ⟨k, i k⟩ ^ e k

def blowUpGens (s g f m : MRing ι R) (e : K → ℕ) : BlowUpIdx ι → MRing ι R
  | none => s * g
  | some none => f * m
  | some (some i) => f * powMonomial e i

end Gens

section Degrees

variable {K : Type*} [DecidableEq K]

def residualDeg (e : K → ℕ) : Option K → ℤ := Pi.single none 1 - liftDeg (fun k => (e k : ℤ))

def exceptionalDeg (b : K → ℤ) (e : K → ℕ) : Option K → ℤ :=
  liftDeg (fun k => b k + e k) - Pi.single none 1

end Degrees

section Sides

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def cutIdentityLeftSide (P : Ideal (MRing ι O)) (f g : MRing ι O) (c : K → ℕ) {d : ℕ} (L : Fin d → K → ℤ) : ℤ :=
  cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g)

open Classical in

def cutIdentityRightSide (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (s : MRing ι O) {d : ℕ}
    (L : Fin d → K → ℤ) : ℤ :=
  cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
      else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

theorem cutIdentity_iff (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentity ϖ P b f g c s L ↔ cutIdentityLeftSide P f g c L = cutIdentityRightSide ϖ P b f g s L :=
  Iff.rfl

end Sides

section Lemmas

def ExcessPositive.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ s : MRing ι O, s ∉ P →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    0 < commonExcess ϖ P f g s

def AvoidingFormExists.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ e₀ : K → ℕ, ∃ (e : K → ℕ) (h : MRing ι O), IsMultiHomog h e ∧ h ∉ P ∧ e₀ ≤ e ∧
      (∀ H, divCycle P h H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) ∧
      (∀ G, (C ϖ : MRing ι O) ∈ G → ratDiv P f g G ≠ 0 → divCycle P h G = 0) ∧
      commonExcess ϖ P f g h = 0 ∧
      ∀ s : MRing ι O, s ∉ P → commonExcess ϖ P f g (s * h) = commonExcess ϖ P f g s

def HorizontalAvoidingForm.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ s : MRing ι O, s ∉ P → ∀ e : K → ℕ,
    ∃ m : MRing ι O, IsMultiHomog m e ∧ m ∉ P ∧
      ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H

def BlowUpModel.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    IsModelOver (blowUpOf P u) d

def BlowUpDecomposition.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    IsModelOver (blowUpOf P (blowUpGens s g f m e)) (d + 1) ∧
    IsMultiHomog (liftForm (J := BlowUpIdx ι) s) (liftMDeg c) ∧
    liftForm (J := BlowUpIdx ι) s ∉ blowUpOf P (blowUpGens s g f m e) ∧
    (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ blowUpOf P (blowUpGens s g f m e) ∧
    IsEffectiveVertical (blowUpOf P (blowUpGens s g f m e)) ϖ (residualDeg e)
      (newVar (some none)) (liftForm m) ∧
    IsEffectiveVertical (blowUpOf P (blowUpGens s g f m e)) ϖ (exceptionalDeg b e)
      (liftForm (f * m)) (liftForm g * newVar (some none)) ∧
    (∀ H, divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) H ≠ 0 →
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      IsVerticalDivisor H ϖ (residualDeg e) (newVar (some none)) (liftForm m) ∧
      IsVerticalDivisor H ϖ (exceptionalDeg b e) (liftForm (f * m)) (liftForm g * newVar (some none))) ∧
    (∀ H, divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) H ≠ 0 →
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      IsVerticalDivisor H ϖ (exceptionalDeg b e) (liftForm (f * m)) (liftForm g * newVar (some none)))

def BlowUpExcessDecreases.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) < commonExcess ϖ P f g s ∧
      commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) < commonExcess ϖ P f g s

def LeftSideAdditiveInDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c₁ c₂ : K → ℕ) (L : Fin d → K → ℤ),
      cutIdentityLeftSide P f g (c₁ + c₂) L = cutIdentityLeftSide P f g c₁ L + cutIdentityLeftSide P f g c₂ L

def RightSideMultiplicativeInForm.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g s₁ s₂ : MRing ι O), s₁ ∉ P → s₂ ∉ P → ∀ L : Fin d → K → ℤ,
      cutIdentityRightSide ϖ P b f g (s₁ * s₂) L = cutIdentityRightSide ϖ P b f g s₁ L + cutIdentityRightSide ϖ P b f g s₂ L

def AdditivityInDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b₁ b₂ : K → ℤ) (f₁ g₁ f₂ g₂ : MRing ι O),
      IsVerticalDivisor P ϖ b₁ f₁ g₁ → IsVerticalDivisor P ϖ b₂ f₂ g₂ →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b₁ f₁ g₁ ∧ IsVerticalDivisor H ϖ b₂ f₂ g₂) →
    ∀ L : Fin d → K → ℤ,
      cutIdentityLeftSide P (f₁ * f₂) (g₁ * g₂) c L = cutIdentityLeftSide P f₁ g₁ c L + cutIdentityLeftSide P f₂ g₂ c L ∧
      cutIdentityRightSide ϖ P (b₁ + b₂) (f₁ * f₂) (g₁ * g₂) s L = cutIdentityRightSide ϖ P b₁ f₁ g₁ s L + cutIdentityRightSide ϖ P b₂ f₂ g₂ s L

def CommonFactorRemoval.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g q s : MRing ι O), f ∉ P → g ∉ P → q ∉ P → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → f ∉ H ∧ g ∉ H ∧ q ∉ H) →
    ∀ (c : K → ℕ) (L : Fin d → K → ℤ),
      cutIdentityLeftSide P (f * q) (g * q) c L = cutIdentityLeftSide P f g c L ∧
      cutIdentityRightSide ϖ P b (f * q) (g * q) s L = cutIdentityRightSide ϖ P b f g s L

def TautologicalCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ cf cg : K → ℕ, IsMultiHomog f cf → IsMultiHomog g cg → (fun k => (cf k : ℤ) - cg k) = b →
    ∀ L : Fin d → K → ℤ,
      cutIdentityLeftSide P f g cf L - cutIdentityLeftSide P f g cg L = cutIdentityRightSide ϖ P b f g f L - cutIdentityRightSide ϖ P b f g g L

def BlowUpInvariance.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ L : Fin d → K → ℤ,
      cutIdentityLeftSide (blowUpOf P (blowUpGens s g f m e)) (liftForm f) (liftForm g) (liftMDeg c) (liftDegs L) =
        cutIdentityLeftSide P f g c L ∧
      cutIdentityRightSide ϖ (blowUpOf P (blowUpGens s g f m e)) (liftDeg b) (liftForm f) (liftForm g) (liftForm s)
        (liftDegs L) = cutIdentityRightSide ϖ P b f g s L

def BlowUpReduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ L : Fin d → K → ℤ,
      cutIdentity ϖ (blowUpOf P (blowUpGens s g f m e)) (residualDeg e) (newVar (some none))
        (liftForm m) (liftMDeg c) (liftForm s) (liftDegs L) →
      cutIdentity ϖ (blowUpOf P (blowUpGens s g f m e)) (exceptionalDeg b e) (liftForm (f * m))
        (liftForm g * newVar (some none)) (Pi.single none 1) (newVar none) (liftDegs L) →
      cutIdentity ϖ P b f g c s L

end Lemmas

section Helpers

theorem divCycle_congr_of_sub_mem {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {s s' : MRing ι R} (h : s - s' ∈ P) : divCycle P s = divCycle P s' := by
  have h1 : s ∈ P ⊔ Ideal.span {s'} := by
    have e : s = (s - s') + s' := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h2 : s' ∈ P ⊔ Ideal.span {s} := by
    have e : s' = s - (s - s') := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left h)
  have e : P ⊔ Ideal.span {s} = P ⊔ Ideal.span {s'} := le_antisymm
    (sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr h1))
    (sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr h2))
  funext W
  unfold divCycle
  by_cases hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · have hc' : W ∈ (P ⊔ Ideal.span {s'}).minimalPrimes ∧ IsRelevant W := e ▸ hc
    rw [dif_pos hc, dif_pos hc', e]
  · have hc' : ¬ (W ∈ (P ⊔ Ideal.span {s'}).minimalPrimes ∧ IsRelevant W) := e ▸ hc
    rw [dif_neg hc, dif_neg hc']

theorem cutIdentityRightSide_congr_of_sub_mem {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ)
    (f g : MRing ι O) {s s' : MRing ι O} (h : s - s' ∈ P) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentityRightSide ϖ P b f g s L = cutIdentityRightSide ϖ P b f g s' L := by
  unfold cutIdentityRightSide
  rw [divCycle_congr_of_sub_mem h]

theorem aeval_blowUpSubst_liftForm {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (u : J → MRing ι R) (p : MRing ι R) :
    aeval (blowUpSubst P u) (liftForm p) = Polynomial.C (Ideal.Quotient.mk P p) := by
  have e : (aeval (blowUpSubst P u)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      (Polynomial.CAlgHom).comp (Ideal.Quotient.mkₐ R P) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, blowUpSubst]
  exact DFunLike.congr_fun e p

theorem blowUp_relation {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (s g f m : MRing ι R) (e : K → ℕ) :
    liftForm (s * g) * newVar (some none) - liftForm (f * m) * newVar none ∈
      blowUpOf P (blowUpGens s g f m e) := by
  rw [blowUpOf, RingHom.mem_ker]
  simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
  ring

end Helpers

section Examples

theorem blowUpModel_hypotheses_example :
    let S := MRing (fun _ : Unit => Fin 2) ℤ_[2]
    IsModelOver (⊥ : Ideal S) 1 ∧ (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : S) (Pi.single () 1)) ∧
      ∃ j : Fin 2, (X ⟨(), j⟩ : S) ∉ (⊥ : Ideal S) := by
  intro S
  obtain ⟨hmodel, hX0, -⟩ := lemmas_hypotheses_example
  exact ⟨hmodel, fun j => isWeightedHomogeneous_X _ _ _, 0, hX0⟩

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
