import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform

noncomputable section

open MeasureTheory NumberField Set
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core
open scoped ENNReal NumberField.AdeleRing InnerProductSpace

namespace PositivityTheory.Rg.Tf.Adel

variable {K : Type} [Field K] [NumberField K] {a b n : ℕ}

def blk {R : Type} [CommRing R] (m₁ : GL (Fin a) R) (m₂ : GL (Fin b) R) : GL (Fin (a + b)) R where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.val 0 0 m₂.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.inv 0 0 m₂.inv)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, m₁.val_inv, m₂.val_inv,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, m₁.inv_val, m₂.inv_val,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable (a b) in

def HP (g : G1 K (a + b)) : ℝ :=
  sInf {t | ∃ (X : UPos (a + b) a → 𝔸[K]) (m₁ : AdelicGLn.AdelicGL K a) (m₂ : AdelicGLn.AdelicGL K b)
    (k : AdelicGLn.AdelicGL K (a + b)), k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))) ∧
      (g : AdelicGLn.AdelicGL K (a + b)) = unipGL X * blk m₁ m₂ * k ∧ t = Real.log (detModule K a m₁).1}

variable (K a b) in

def ParΓ : Subgroup (Gam K (a + b)) :=
  Subgroup.closure {γ | ∀ i j : Fin (a + b), a ≤ (i : ℕ) → (j : ℕ) < a →
    (((γ : G1 K (a + b)) : AdelicGLn.AdelicGL K (a + b)) : Matrix (Fin (a + b)) (Fin (a + b)) 𝔸[K]) i j = 0}

def theta (β : ℝ → ℂ) (f : G1 K (a + b) → ℂ) (g : G1 K (a + b)) : ℂ :=
  ∑ᶠ q : Quotient (QuotientGroup.rightRel (ParΓ K a b)),
    β (HP a b ((q.out : G1 K (a + b)) * g)) *
      Complex.exp ((((a + b : ℕ) : ℝ) / 2 * HP a b ((q.out : G1 K (a + b)) * g) : ℝ) : ℂ) * f ((q.out : G1 K (a + b)) * g)

def Reps (μ : Measure (G1 K n)) (v : L2 μ) (φ : G1 K n → ℂ) : Prop :=
  ∀ᵐ y ∂μ, (v : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = φ y

structure CuspIrr (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) : Prop where
  le : τ ≤ cuspidalL2 μ
  closed : IsClosed (τ : Set (L2 μ))
  ne : τ ≠ ⊥
  inv : ∀ g, ∀ v ∈ τ, rightRegularRep (Gam K n) μ g v ∈ τ
  irr : ∀ ρ : Submodule ℂ (L2 μ), ρ ≤ τ → IsClosed (ρ : Set (L2 μ)) →
    (∀ g, ∀ v ∈ ρ, rightRegularRep (Gam K n) μ g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ

structure IsSec {μ₁ : Measure (G1 K a)} {μ₂ : Measure (G1 K b)} (τ₁ : Submodule ℂ (L2 μ₁)) (τ₂ : Submodule ℂ (L2 μ₂))
    (f : G1 K (a + b) → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C
  unip : ∀ (X : UPos (a + b) a → 𝔸[K]) (g : G1 K (a + b)), f (unipOne K (a + b) a X * g) = f g
  ray : ∀ (r : {r : ℝ // 0 < r}) (x g : G1 K (a + b)),
    (x : AdelicGLn.AdelicGL K (a + b)) = blk (centralSection K a r) (centralSection K b r⁻¹) * g → f x = f g
  levi : ∀ g : G1 K (a + b), ∃ (d : ℕ) (φ : Fin d → G1 K a → ℂ) (ψ : Fin d → G1 K b → ℂ),
    (∀ i, Continuous (φ i) ∧ ∃ v ∈ τ₁, Reps μ₁ v (φ i)) ∧ (∀ i, Continuous (ψ i) ∧ ∃ v ∈ τ₂, Reps μ₂ v (ψ i)) ∧
    ∀ (m₁ : G1 K a) (m₂ : G1 K b) (x : G1 K (a + b)),
      (x : AdelicGLn.AdelicGL K (a + b)) = blk (m₁ : AdelicGLn.AdelicGL K a) (m₂ : AdelicGLn.AdelicGL K b) * g →
        f x = ∑ i, φ i m₁ * ψ i m₂

variable (K n) in

structure TypeDat where
  U : Subgroup (G1 K n)
  isOpen : ∃ O : Set (AdelicGLn.AdelicGL K n), IsOpen O ∧ ∀ g : G1 K n, g ∈ U ↔
    (g : AdelicGLn.AdelicGL K n) ∈ O ∧ (g : AdelicGLn.AdelicGL K n) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))
  ν : Measure (G1 K n)
  prob : IsProbabilityMeasure ν
  supp : ∀ᵐ k ∂ν, k ∈ U
  inv : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν
  e : G1 K n → ℂ
  cont : Continuous e
  star : ∀ k ∈ U, e k⁻¹ = starRingEnd ℂ (e k)
  idem : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k

def TypeDat.Fix (D : TypeDat K n) (f : G1 K n → ℂ) : Prop := ∀ g, ∫ k, D.e k * f (g * k) ∂D.ν = f g

def TypeDat.Hecke (D : TypeDat K n) (f : CC K n) : Prop :=
  ∀ g, ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν = f g ∧ ∫ k, f (g * k⁻¹) * D.e k ∂D.ν = f g

def TypeDat.FixedByTypeProjector (D : TypeDat K n) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (w : L2 μ) : Prop :=
  ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν = w

def TypeDat.Level (D : TypeDat K n) (Kf : Subgroup (AdelicGLn.FiniteAdelicGL K n)) : Prop :=
  (∀ k : G1 K n, (AdelicGLn.prodEquiv K n k).1 = 1 → (k ∈ D.U ↔ (AdelicGLn.prodEquiv K n k).2 ∈ Kf)) ∧
  (∀ k : G1 K n, (AdelicGLn.prodEquiv K n k).2 = 1 →
    (k : AdelicGLn.AdelicGL K n) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) → k ∈ D.U) ∧
  ∀ k ∈ D.U, (AdelicGLn.prodEquiv K n k).1 = 1 → ∀ u ∈ D.U, D.e (k * u) = D.e u

def Smooth (f : CC K n) : Prop :=
  f ∈ Submodule.span ℂ {f' : CC K n | ∃ (ν : Measure (ArchUnits K n)) (_ : ν.IsHaarMeasure) (β : ArchMatrix K n → ℝ)
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) (g : CC K n),
    f' = archConv ν hβ.continuous hβc hβu (finAvg U hU g)}

end PositivityTheory.Rg.Tf.Adel
