import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

noncomputable section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V.LDataCardLeFinrank

namespace UpperTheory.V.Win

def jZero (l R : ℕ) : ℕ := Nat.log l R + 3

def SecondBound (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
    ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ →
      ∀ (Ω : Type) [Field Ω] [Algebra L₂ Ω] [IsAlgClosure L₂ Ω] (D : LData L₂ Ω l),
        shaInv L₁ l e ≤ VLen D e + ((R * (m - jZero l R) : ℕ) : ℕ∞)

def ABound (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] : Prop :=
  (∃ (K : Type) (_ : NormedField K) (_ : NormedAlgebra ℚ_[l] K) (_ : IsUltrametricDist K) (c R' : ℕ) (s : Fin R' → K),
    R' ≤ R ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      ∀ B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - (e : K)‖) →
        shaInv L₁ l e ≤ ((R' * (max m (jZero l R) + c + B) : ℕ) : ℕ∞)) ∧
  SecondBound l R L₀

def FirstBound (l R c : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] (Z : ℕ) (Exc : Finset ℕ) : Prop :=
  Exc.card ≤ R ∧ ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
    ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e ≤ ((R * (max m (jZero l R) + c + Nat.log l Z) : ℕ) : ℕ∞)

def FixedIn : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l → ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ →
    ∃ R : ℕ, ABound l R L₀

def TwoBase (M : AbF) (q d : ℕ) (L₀ : Type) [Field L₀] [NumberField L₀] : Prop :=
  HasMuQ 2 L₀ ∧ Module.finrank ℚ L₀ ≤ 8 * M.deg ∧ Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * q * d) ℚ) ∧
    ∀ e : ℕ, 2 ≤ e → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E →
      ∃ (m : ℕ) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁), IsLayer 2 m L₀ L₁ ∧ m ≤ e + 2 ∧
        ∀ k : ℕ, 1 ≤ k → shaInv E 2 k ≤ 1 + shaInv L₁ 2 k

def TwoIn : Prop :=
  ∀ M : AbF, ∃ R : ℕ, ∀ q d : ℕ, PrimePair M.m q d →
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), TwoBase M q d L₀ ∧ ABound 2 R L₀

def Good (eta Ct : ℝ) (Exc : Finset ℕ) (x : ℝ) : Prop := ∀ e ∈ Exc, (e : ℝ) ≤ x ^ Ct → (e : ℝ) ≤ x ^ eta

theorem Good.mono {eta Ct x : ℝ} {S T : Finset ℕ} (h : S ⊆ T) (hT : Good eta Ct T x) : Good eta Ct S x := fun e he hle => hT e (h he) hle

def ptBound (C eps x : ℝ) : ℝ := C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))

end UpperTheory.V.Win

end
