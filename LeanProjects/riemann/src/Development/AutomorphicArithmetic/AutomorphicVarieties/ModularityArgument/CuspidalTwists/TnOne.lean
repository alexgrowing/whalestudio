import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section Alg

variable {R : Type} [CommRing R]

def tn (g t : M2 R) : M4 R :=
  !![g 0 0 * t 0 0, g 0 0 * t 0 1, -(g 0 1 * t 0 1), g 0 1 * t 0 0;
    g 0 0 * t 1 0, g 0 0 * t 1 1, -(g 0 1 * t 1 1), g 0 1 * t 1 0;
    -(g 1 0 * t 1 0), -(g 1 0 * t 1 1), g 1 1 * t 1 1, -(g 1 1 * t 1 0);
    g 1 0 * t 0 0, g 1 0 * t 0 1, -(g 1 1 * t 0 1), g 1 1 * t 0 0]

def nA (s : R) : M4 R := !![1, 0, 0, 0; s, 1, 0, 0; 0, 0, 1, 0; 0, 0, -s, 1]

def flg (x s : R) : M4 R := tn (low x) 1 * nA s

theorem tn_one : tn (1 : M2 R) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

theorem tn_mul (g g' t t' : M2 R) : tn (g * g') (t * t') = tn g t * tn g' t' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

def rep4 {Γ : Type} [Group Γ] (δ : Γ →* Rˣ) (ρ τ : Γ →* M2 R) : Γ →* M4 R where
  toFun g := (δ g : R) • tn (ρ g) (τ g)
  map_one' := by simp [tn_one]
  map_mul' g h := by simp [tn_mul, smul_smul, mul_comm]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def tenB (ρ₁ τ : G ℚ Ω →* M2 c.O) : G ℚ Ω →* GL (Fin 4) (Qbar l) :=
  (mapRep (algebraMap c.O (PadicAlgCl l)) (rep4 1 ρ₁ τ)).toHomUnits

def phi (D : Raw Ω c) (pr : Bool) : G ℚ Ω →* c.Oˣ := if pr then D.ξ * D.ψ⁻¹ else D.ξ * D.ψ

def Phi (D : Raw Ω c) (pr : Bool) (k : ℕ) : G ℚ Ω →* c.Oˣ := chiO ℚ Ω l c.O ^ (k - 1) * phi D pr

structure TauDat (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'] (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l)
    (τ : G ℚ Ω →* M2 c₁.O) (s : ValuationSubring Ω → c₁.O) (κ : G K' Ω →* (Qbar l)ˣ) : Prop where
  pos : 1 ≤ m
  cont : ∀ i j, AdicCont (maximalIdeal c₁.O) fun g => τ g i j
  form : ∀ g, (τ g)ᵀ * !![1, 0; 0, -1] * τ g = !![1, 0; 0, -1]
  on : ∀ g ∈ K'.fixingSubgroup, τ g 1 1 = τ g 0 0 ∧ τ g 1 0 = τ g 0 1
  off : ∀ g ∉ K'.fixingSubgroup, τ g 1 1 = -τ g 0 0 ∧ τ g 1 0 = -τ g 0 1
  red : ∀ g, τ g 0 0 - 1 ∈ maximalIdeal c₁.O ∧ τ g 0 1 ∈ maximalIdeal c₁.O
  nrm : τ g0 = !![1, 0; 0, -1]
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ∈ K'.fixingSubgroup → τ g = 1
  sgn : ∀ A, s A = 1 ∨ s A = -1
  mov : ∀ (A A' : ValuationSubring Ω) (g : G ℚ Ω), A.valuation (l : Ω) < 1 → (∀ x, g x ∈ A' ↔ x ∈ A) →
    (g ∈ K'.fixingSubgroup → s A' = s A) ∧ (g ∉ K'.fixingSubgroup → s A' = -s A)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
    τ g 0 0 + τ g 0 1 * s A = (chiO ℚ Ω l c₁.O g ^ m : c₁.Oˣ)
  val : ∀ h : G K' Ω, (κ h : Qbar l) = ((τ (resQ K' h) 0 0 + τ (resQ K' h) 0 1 : c₁.O) : Qbar l)
  kcont : Continuous κ
  alg : ∃ (art : Ideles K' →* Gab K' Ω) (Y : HChar K') (a : (K' →+* ℂ) → ℤ) (e : K' →+* ℂ), IsGlobalArtin art ∧ IsAlgPos Y a ∧
    IsLAdicOf art ι Y a κ ∧ a e = -(m : ℤ) ∧ a (ComplexEmbedding.conjugate e) = m

structure Mod4 (D : Raw Ω c) (pr : Bool) (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (g0 : G ℚ Ω) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    {c₁ : Coef l} (h : c.O ≤ c₁.O) (ρ₁ : G ℚ Ω →* M2 c₁.O) (x : ValuationSubring Ω → c₁.O) : Prop where
  iso : RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits
  cont : ∀ i j, AdicCont (maximalIdeal c₁.O) fun g => ρ₁ g i j
  red : ∀ g, ρ₁ g 0 0 - inc h (Phi D pr k g) ∈ maximalIdeal c₁.O ∧ ρ₁ g 1 1 - 1 ∈ maximalIdeal c₁.O ∧ ρ₁ g 0 1 ∈ maximalIdeal c₁.O
  ne : ∃ g, ρ₁ g 1 0 ∉ maximalIdeal c₁.O
  nrm : ρ₁ g0 0 1 = 0 ∧ ρ₁ g0 1 0 = 0
  det : ∀ g, θ g = 1 → (ρ₁ g).det = inc h (Phi D pr k g)
  away : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, phi D pr g = 1 → θ g = 1 → ρ₁ g = 1
  flag : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Dec (F := ℚ) A,
    ρ₁ s 1 0 + ρ₁ s 1 1 * x A = (ρ₁ s 0 0 + ρ₁ s 0 1 * x A) * x A
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A,
    ρ₁ s 0 0 + ρ₁ s 0 1 * x A = (chiO ℚ Ω l c₁.O s ^ (k - 1) : c₁.Oˣ) ∧ ρ₁ s 1 1 - x A * ρ₁ s 0 1 = 1

structure Tw4 {D : Raw Ω c} (T₀ : Tower D) (k : ℕ) (δ : G ℚ Ω →* c.Oˣ) : Prop where
  cont : AdicCont (maximalIdeal c.O) fun g => (δ g : c.O)
  mul : ∀ g, δ g ^ 2 * Phi D T₀.pr k g = D.th g
  red0 : ∀ g, Raw.bar (chi D T₀.pr 0) g = Raw.bar δ g * Raw.bar (Phi D T₀.pr k) g
  red3 : ∀ g, Raw.bar (chi D T₀.pr 3) g = Raw.bar δ g
  kill : ∀ g, cycZ ℚ Ω l g = 1 → D.rbar g = 1 → δ g = 1 ∧ phi D T₀.pr g = 1
  wt : ∃ (U : Subgroup (G ℚ Ω)) (j : ℤ), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, δ g ^ 2 = chiO ℚ Ω l c.O g ^ j

def TauEx : Prop :=
  Af.Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : G ℚ Ω, Sd.IsCC cc) →
    ∀ g0 ∉ K'.fixingSubgroup, ∃ (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), ∀ c₂ : Coef l, c₁.O ≤ c₂.O → ∀ j : ℕ, 1 ≤ j →
      ∃ τ s, TauDat ι K' g0 (m * j) c₂ τ s (κ ^ j)

end UpperTheory.V.Cu

end
