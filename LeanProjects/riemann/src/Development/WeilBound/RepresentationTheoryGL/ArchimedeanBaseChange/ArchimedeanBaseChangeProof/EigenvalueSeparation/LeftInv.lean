import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.VeryCuspZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.E

open PositivityTheory.Rg.BcB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev H (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Type := GA E a × GA E b

def ratH (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Subgroup (H E a b) :=
  ((ratGL E a).prodMap (ratGL E b)).range

abbrev borelH (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : MeasurableSpace (H E a b) := borel _

attribute [local instance] borelH

structure Dom (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) where
  μ : Measure (H E a b)
  haar : μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ μ.IsOpenPosMeasure ∧ IsLocallyFiniteMeasure μ
  F : Set (H E a b)
  fd : IsFundamentalDomain (ratH E a b) F μ

def Dom.ν (D : Dom E a b) : Measure (H E a b) := D.μ.restrict D.F

def IsTestH (φ : H E a b → ℂ) : Prop := Continuous φ ∧ HasCompactSupport φ

def IsTestM {ι : Type} (Φ : Matrix ι ι (H E a b → ℂ)) : Prop := ∀ i j, IsTestH (Φ i j)

def conv {ι : Type} [Fintype ι] (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (f : ι → H E a b → ℂ) :
    ι → H E a b → ℂ :=
  fun i x => ∑ j, ∫ y, Φ i j y * f j (x * y) ∂μ

def kerH (φ : H E a b → ℂ) (x y : H E a b) : ℂ := ∑ᶠ γ : ratH E a b, φ (x⁻¹ * (γ : H E a b) * y)

def kerM {ι : Type} (Φ : Matrix ι ι (H E a b → ℂ)) (x y : H E a b) : Matrix ι ι ℂ := fun i j => kerH (Φ i j) x y

abbrev Hs {ι : Type} (D : Dom E a b) : Type := PiLp 2 fun _ : ι => Lp ℂ 2 D.ν

def IsROp {ι : Type} [Fintype ι] (D : Dom E a b) (Φ : Matrix ι ι (H E a b → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) :
    Prop :=
  ∀ f i, (T f i : H E a b → ℂ) =ᵐ[D.ν] fun x => ∑ j, ∫ y, kerH (Φ i j) x y * (f j : H E a b → ℂ) y ∂D.ν

def adjM {ι : Type} (Φ : Matrix ι ι (H E a b → ℂ)) : Matrix ι ι (H E a b → ℂ) :=
  fun i j y => starRingEnd ℂ (Φ j i y⁻¹)

def mulM {ι : Type} [Fintype ι] (μ : Measure (H E a b)) (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) : Matrix ι ι (H E a b → ℂ) :=
  fun i j y => ∑ k, ∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂μ

def redSize {n : ℕ} (g : GA E n) : ℝ := ⨅ γ : GL (Fin n) E, logSize (ratGL E n γ * g)

def wt (x : H E a b) : ℝ := 1 + redSize x.1 + redSize x.2

def LeftInv {ι : Type} (f : ι → H E a b → ℂ) : Prop := ∀ i (γ : ratH E a b) x, f i ((γ : H E a b) * x) = f i x

def WL2 {ι : Type} [Fintype ι] (D : Dom E a b) (M : ℕ) (f : ι → H E a b → ℂ) : Prop :=
  ∀ i, ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))) * ‖f i x‖ₑ ^ 2 ∂D.ν < ⊤

end PositivityTheory.Rg.BcB.E

end
