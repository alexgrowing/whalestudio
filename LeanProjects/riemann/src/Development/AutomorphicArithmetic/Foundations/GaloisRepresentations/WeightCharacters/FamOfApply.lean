import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.WtDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

def ExpLe (s : ℤ) : Submodule ℂ (Circle → ℂ) := Submodule.span ℂ {f | ∃ m : ℤ, m ≤ s ∧ f = fun z : Circle => (z : ℂ) ^ m}

def ExpGe (s : ℤ) : Submodule ℂ (Circle → ℂ) := Submodule.span ℂ {f | ∃ m : ℤ, s ≤ m ∧ f = fun z : Circle => (z : ℂ) ^ m}

def dg {a : ℕ} (d : Fin a → ℂˣ) : GL (Fin a) ℂ where
  val := Matrix.diagonal fun i => (d i : ℂ)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

def tor (a k : ℕ) (z : Circle) : GL (Fin a) ℂ := dg fun i => if i.val < k then Circle.toUnits z else 1

theorem tor_coe (a k : ℕ) (z : Circle) : ((tor a k z : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
    Matrix.diagonal fun i => if i.val < k then (z : ℂ) else 1 := by
  change Matrix.diagonal _ = _
  congr 1
  funext i
  by_cases h : i.val < k <;> simp [h]

def psum {a : ℕ} (κ : DomWeight a) (k : ℕ) : ℤ := ∑ i : Fin a with i.val < k, κ.w i

def IsUp {a : ℕ} (b : GL (Fin a) ℂ) : Prop := ∀ i j : Fin a, j < i → (b : Matrix (Fin a) (Fin a) ℂ) i j = 0

def chi {a : ℕ} (κ : DomWeight a) (b : GL (Fin a) ℂ) : ℂ := ∏ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ^ κ.w i

def top {a : ℕ} (κ : DomWeight a) : nablaSq ℂ a κ :=
  ⟨extremal ℂ a κ, Formalism.GradedWeylDivisibility.hwMem ℂ a a le_rfl _ (Formalism.L2.DIV.natW_antitone κ)⟩

def ev1 {a : ℕ} (κ : DomWeight a) : nablaSq ℂ a κ →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval fun p : Fin a × Fin a => (1 : Matrix (Fin a) (Fin a) ℂ) p.1 p.2).toLinearMap.comp (nablaSq ℂ a κ).subtype

def delta {a : ℕ} (κ : DomWeight a) (h : GL (Fin a) ℂ) : ℂ := ev1 κ (sqRep ℂ a κ h (top κ))

def pev {a : ℕ} (P : MvPolynomial (Fin a × Fin a) ℂ) (h : GL (Fin a) ℂ) : ℂ :=
  MvPolynomial.eval (fun p => (h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2) P

def RFin {a : ℕ} (p : GL (Fin a) ℂ → ℂ) : Prop :=
  Continuous p ∧ ∃ A : Submodule ℂ (GL (Fin a) ℂ → ℂ), FiniteDimensional ℂ A ∧ ∀ y, (fun n => p (n * y)) ∈ A

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def IsCirc (τ : E →+* ℂ) (k : ℕ) (x : Circle → infU E a) : Prop :=
  ∀ z, (x z).1 ∈ embU a τ ∧ cEmb τ (x z).1 = tor a k z

structure Fam (τ : E →+* ℂ) (W : Wt E a) (K : Subgroup (UA E a)) (ν : DomWeight a) (d : ℕ)
    (B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)) : Prop where
  aut : ∀ y₁ y₂ v, IsAutFormU (B y₁ y₂ v)
  fix : ∀ k ∈ K, ∀ y₁ y₂ v, RU E a k (B y₁ y₂ v) = B y₁ y₂ v
  inf : ∀ (x : infU E a) y₁ y₂ v, RU E a x (B y₁ y₂ v) = B (cEmb τ x.1 * y₁) (cEmb τ x.1 * y₂) (W.rep x v)
  up : ∀ b, IsUp b → ∀ y₁ y₂ v, B (y₁ * b) y₂ v = chi ν b • B y₁ y₂ v
  le : ∀ k x, IsCirc τ k x → ∀ y₁ y₂ v g,
    (fun z => B (tor a k z * y₁) (tor a k z * y₂) (W.rep (x z) v) g) ∈ ExpLe (psum ν k + d)
  ge : ∀ k x, IsCirc τ k x → ∀ y₂ v g, (fun z => B 1 (tor a k z * y₂) (W.rep (x z) v) g) ∈ ExpGe (-d)
  fin : ∃ S : Submodule ℂ (UA E a → ℂ), FiniteDimensional ℂ S ∧ ∀ y₁ y₂ v, B y₁ y₂ v ∈ S

structure IsNrm (τ : E →+* ℂ) (C : Subgroup (UA E a)) (n : UA E a → GL (Fin a) ℂ) : Prop where
  left : ∀ γ ∈ ratU E a, ∀ g, n (γ * g) = n g
  lev : ∀ c ∈ C, ∀ g, n (g * c) = n g
  inf : ∀ x ∈ infU E a, ∀ g, n (g * x) = n g * cEmb τ x

structure IsEll (C : Subgroup (UA E a)) (ℓ : UA E a → C) : Prop where
  left : ∀ γ ∈ ratU E a, ∀ g, ℓ (γ * g) = ℓ g
  lev : ∀ (c : C) g, ℓ (g * c) = ℓ g * c
  inf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g

def famOf {W : Wt E a} (n : UA E a → GL (Fin a) ℂ) (ν : DomWeight a) {Q : Type} [Fintype Q] (f : Q → algForms W)
    (P : Q → MvPolynomial (Fin a × Fin a) ℂ) (X : Q → GL (Fin a) ℂ) (y₁ y₂ : GL (Fin a) ℂ) : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
  ∑ q, (LinearMap.mulLeft ℂ fun g => pev (P q) (n g * y₂) * delta ν (X q * (n g * y₁))) ∘ₗ (f q).1

theorem famOf_apply {W : Wt E a} (n : UA E a → GL (Fin a) ℂ) (ν : DomWeight a) {Q : Type} [Fintype Q] (f : Q → algForms W)
    (P : Q → MvPolynomial (Fin a × Fin a) ℂ) (X : Q → GL (Fin a) ℂ) (y₁ y₂ : GL (Fin a) ℂ) (v : W.Sp) (g : UA E a) :
    famOf n ν f P X y₁ y₂ v g = ∑ q, pev (P q) (n g * y₂) * delta ν (X q * (n g * y₁)) * (f q).1 v g := by
  simp [famOf, LinearMap.sum_apply, Finset.sum_apply]

def IntGL {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (h : GL (Fin a) ℂ) : Prop :=
  ∀ i j, ‖ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ 1 ∧ ‖ι.symm (((h⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ 1

def NearOne {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ε : ℝ) (h : GL (Fin a) ℂ) : Prop :=
  ∀ i j, ‖ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) i j - (1 : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ ε

end UpperTheory.Gal.Wt

end
