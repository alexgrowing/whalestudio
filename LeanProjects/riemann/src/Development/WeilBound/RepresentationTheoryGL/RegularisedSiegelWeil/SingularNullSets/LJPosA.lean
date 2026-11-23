import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def IsIntM {ι κ : Type} (x : Matrix ι κ (Fv F v)) : Prop := ∀ i j, x i j ∈ v.adicCompletionIntegers F

variable (F v) in

def KL (n : ℕ) : Subgroup (GL (Fin (n + n)) (Fv F v)) where
  carrier := {g | IsIntM g.1 ∧ IsIntM (g⁻¹).1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha.1 i k) (hb.1 k j)
    · simp only [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hb.2 i k) (ha.2 k j)
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · simp only [inv_one, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩

def nM {n : ℕ} (x : Matrix (Fin n) (Fin n) (Fv F v)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v) := blk4 1 x 0 1

def nL {n : ℕ} (x : Matrix (Fin n) (Fin n) (Fv F v)) : GL (Fin (n + n)) (Fv F v) where
  val := nM x
  inv := nM (-x)
  val_inv := by
    simp only [nM, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    simp only [nM, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

def botMinor {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) (e : Fin n → Fin (n + n)) :
    Matrix (Fin n) (Fin n) (Fv F v) :=
  Matrix.of fun i j => g (Fin.natAdd n i) (e j)

def hB {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) : ℝ≥0 :=
  Finset.univ.sup' ⟨fun i => Fin.natAdd n i, Finset.mem_univ _⟩ fun e : Fin n → Fin (n + n) => ‖(botMinor g e).det‖₊

def IsUpper {n : ℕ} (p : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) : Prop :=
  ∀ i j, p (Fin.natAdd n i) (Fin.castAdd n j) = 0

def blkD {n : ℕ} (p : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v) :=
  Matrix.of fun i j => p (Fin.natAdd n i) (Fin.natAdd n j)

instance instMeasGL (n : ℕ) : MeasurableSpace (GL (Fin (n + n)) (Fv F v)) := borel _
instance instBorelGL (n : ℕ) : BorelSpace (GL (Fin (n + n)) (Fv F v)) := ⟨rfl⟩

def LocIwa : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
  (g : GL (Fin (n + n)) (Fv F v)), ∃ p : GL (Fin (n + n)) (Fv F v), ∃ k ∈ KL F v n, IsUpper p.1 ∧ g = p * k

def LocHB : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
  (p : GL (Fin (n + n)) (Fv F v)), IsUpper p.1 → ∀ k ∈ KL F v n, hB (p * k).1 = ‖(blkD p.1).det‖₊

def LocCore : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n r t : ℕ), r + t = n → 1 ≤ r →
  ∀ ψv : AddChar (Fv F v) ℂ, (∀ a, (∀ b ∈ v.adicCompletionIntegers F, ψv (a * b) = 1) ↔ a ∈ v.adicCompletionIntegers F) →
  ∃ (s : Finset (Matrix (Fin n) (Fin n) (Fv F v))) (co : Matrix (Fin n) (Fin n) (Fv F v) → ℂ) (c : ℂ → ℂ),
    (∀ β : Matrix (Fin n) (Fin n) (Fv F v), β.rank < r → (∀ x, IsIntM x → ψv (Matrix.trace (x * β)) = 1) →
      ∑ x ∈ s, co x * ψv (Matrix.trace (x * β)) = 0) ∧
    Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
    ∀ μ : Measure (KL F v n), μ.IsHaarMeasure → IsProbabilityMeasure μ → ∀ z : ℂ,
      ∫ k, ∑ x ∈ s, co x * npow ((hB (((k : GL (Fin (n + n)) (Fv F v)) * nL x) : GL (Fin (n + n)) (Fv F v)).1)⁻¹ ^ 2)
        (z + (n : ℂ) / 2) ∂μ = c z

end PositivityTheory.Rg.Rsw.L.LJPos

end
