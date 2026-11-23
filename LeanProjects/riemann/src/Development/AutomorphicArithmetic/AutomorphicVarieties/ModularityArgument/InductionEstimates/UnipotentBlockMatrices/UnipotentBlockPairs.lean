import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.IsOrthogonalProjectionTwoLines
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
import GroundTheory.AutomorphicForms.HaarSK

noncomputable section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {K : Type} [Field K] [NumberField K]

def zt (K : Type) [Field K] [NumberField K] (t : ℝ) : AdelicGLn.AdelicGL K 2 := centralSection K 2 ⟨Real.exp t, Real.exp_pos t⟩

def lv (m₁ m₂ : G1 K 2) (t : ℝ) : G1 K (2 + 2) :=
  retractOne (blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t)))

def wGL (R : Type) [CommRing R] : GL (Fin (2 + 2)) R where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) R) 1 0)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) R) 1 0)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def w0 (K : Type) [Field K] [NumberField K] : G1 K (2 + 2) := retractOne (wGL 𝔸[K])

def KG (K : Type) [Field K] [NumberField K] (n : ℕ) : Subgroup (G1 K n) :=
  (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)).comap (normOneGL K n).subtype

def PK (K : Type) [Field K] [NumberField K] : Subgroup (G1 K (2 + 2)) := (ParΓ K 2 2).map (Gam K (2 + 2)).subtype

abbrev Cos (K : Type) [Field K] [NumberField K] : Type := Quotient (QuotientGroup.rightRel (ParΓ K 2 2))

abbrev nn (X : UPos (2 + 2) 2 → 𝔸[K]) : G1 K (2 + 2) := unipOne K (2 + 2) 2 X

abbrev HH (g : G1 K (2 + 2)) : ℝ := HP 2 2 g

def th (F : G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2)) : ℂ := ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * g)

def bf (β : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2)) : ℂ :=
  β (HP 2 2 g) * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 g : ℝ) : ℂ) * f g

theorem theta_eq (β : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) : theta β f = th (bf β f) := rfl

structure PFun (F : G1 K (2 + 2) → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  unip : ∀ X g, F (nn X * g) = F g
  rat : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g
  cusp₁ : ∀ g, ∫ Y in unipFundamentalDomain K 2 1, F (lv (unipOne K 2 1 Y) 1 0 * g) ∂unipMeasure K 2 1 = 0
  cusp₂ : ∀ g, ∫ Y in unipFundamentalDomain K 2 1, F (lv 1 (unipOne K 2 1 Y) 0 * g) ∂unipMeasure K 2 1 = 0

def InBand (F : G1 K (2 + 2) → ℂ) : Prop := ∃ R : ℝ, ∀ g, F g ≠ 0 → |HH g| ≤ R

def Decays (F : G1 K (2 + 2) → ℂ) : Prop :=
  ∀ (N : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, |HH x| ≤ R → ∃ γ ∈ PK K,
    ‖F x‖ * AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N ≤ C

structure Rd {μ₂ : Measure (G1 K 2)} (τ : Submodule ℂ (L2 μ₂)) (φ : G1 K 2 → ℂ) : Prop where
  cont : Continuous φ
  rep : ∃ v ∈ τ, Reps μ₂ v φ
  rat : ∀ γ ∈ Gam K 2, ∀ m, φ (γ * m) = φ m
  cusp : ∀ m, ∫ Y in unipFundamentalDomain K 2 1, φ (unipOne K 2 1 Y * m) ∂unipMeasure K 2 1 = 0
  decay : ∀ N : ℕ, ∃ C : ℝ, ∀ m, ‖φ m‖ * qht m ^ N ≤ C

abbrev fd {n : ℕ} (μ : Measure (G1 K n)) : Measure (G1 K n) := μ.restrict (fundamentalDomain (Gam K n))

abbrev Par (K : Type) [Field K] [NumberField K] : Type := G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])

def pt (p : Par K) : G1 K (2 + 2) := nn p.2.2.2.2 * lv p.1 p.2.1 p.2.2.1 * (p.2.2.2.1 : G1 K (2 + 2))

def parM (μ₂ : Measure (G1 K 2)) (κ : Measure (KG K (2 + 2))) : Measure (Par K) :=
  (fd μ₂).prod ((fd μ₂).prod
    (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
      (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))))

def pm (μ₂ : Measure (G1 K 2)) (f f' : G1 K (2 + 2) → ℂ) (x y : G1 K (2 + 2)) : ℂ :=
  ∫ m₁, ∫ m₂, conj (f (lv m₁ m₂ 0 * x)) * f' (lv m₁ m₂ 0 * y)
    ∂fd μ₂ ∂fd μ₂

def pw (μ₂ : Measure (G1 K 2)) (f f' : G1 K (2 + 2) → ℂ) (x y : G1 K (2 + 2)) : ℂ :=
  ∫ m₁, ∫ m₂, conj (f (lv m₁ m₂ 0 * x)) * f' (lv m₂ m₁ 0 * y)
    ∂fd μ₂ ∂fd μ₂

structure SFun (f : G1 K (2 + 2) → ℂ) : Prop extends PFun f where
  ray : ∀ t g, f (lv 1 1 t * g) = f g
  dec : Decays f

def Slices {μ₂ : Measure (G1 K 2)} (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (f : G1 K (2 + 2) → ℂ) : Prop :=
  ∀ g, (∀ m₂, ∃ v ∈ τ₁, Reps μ₂ v fun m₁ => f (lv m₁ m₂ 0 * g)) ∧ ∀ m₁, ∃ v ∈ τ₂, Reps μ₂ v fun m₂ => f (lv m₁ m₂ 0 * g)

def Unf (μ : Measure (G1 K (2 + 2))) (μ₂ : Measure (G1 K 2)) (κ : Measure (KG K (2 + 2))) (c : ℝ) : Prop :=
  0 < c ∧ (∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
    ∫⁻ y, ∑' q : Cos K, Ψ ((q.out : G1 K (2 + 2)) * y) ∂fd μ =
      ENNReal.ofReal c * ∫⁻ p, Ψ (pt p) ∂parM μ₂ κ) ∧
  ∀ Ψ : G1 K (2 + 2) → ℂ, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) → Integrable (fun p => Ψ (pt p)) (parM μ₂ κ) →
    ∫ y, ∑' q : Cos K, Ψ ((q.out : G1 K (2 + 2)) * y) ∂fd μ = c * ∫ p, Ψ (pt p) ∂parM μ₂ κ

def volN (K : Type) [Field K] [NumberField K] : ℝ := (unipMeasure K (2 + 2) 2).real (unipFundamentalDomain K (2 + 2) 2)

def tChi (μ : Measure (G1 K (2 + 2))) (a : CC K (2 + 2)) (χ : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) : ℂ :=
  ∫ g, a g * χ (HH (x * g) - HH x) * Complex.exp (2 * ((HH (x * g) - HH x : ℝ) : ℂ)) * f (x * g) ∂μ

def Dies (F : G1 K (2 + 2) → ℂ) (r : ℕ) (γ : G1 K (2 + 2)) (X₀ : UPos (2 + 2) r → K) : Prop :=
  ∀ x, ∫ y in GroundTheory.Global.fundamentalSet K, F (γ * unipOne K (2 + 2) r (fun p => y * algebraMap K 𝔸[K] (X₀ p)) * x)
    ∂GroundTheory.Global.adeleMeasure K = 0

section Steps

variable (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
  {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')

def UnitAt : Prop :=
  ∃ (a : CC K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d) (β' : ℝ → Eu d' →L[ℂ] Eu d'), UpperTheory.ConvolutionTheory.C.IsLeftSmooth a ∧ D.Hecke a ∧
    CuspidalProjection.ccStar a = a ∧ ActsBy μ A a β ∧ ActsBy μ A' a β' ∧ IsUnit (symb β 0) ∧ IsUnit (symb β' 0)

def TruncCpt : Prop :=
  ∀ (a : CC K (2 + 2)) (P Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), UpperTheory.ConvolutionTheory.C.IsLeftSmooth a → D.Hecke a → IsOrthogonalProjectionTwoLines A.J A'.J P → 0 ≤ T →
    IsTrunc A.J A'.J T Λ → IsCompactOperator (Λ ∘L Rop μ a ∘L P)

end Steps

def ForAllC (p : ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) (d d' : ℕ), Line μ τ₁ τ₂ D d → Line μ τ₂ τ₁ D d' → Prop) :
    Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (D : TypeDat K (2 + 2)) (d d' : ℕ)
    (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), p K μ μ₂ τ₁ τ₂ D d d' A A'

def LineExC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ D : TypeDat K (2 + 2),
    ∃ d, Nonempty (Line μ τ₁ τ₂ D d)

def UnipotentBlockPairs : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => ShiftCausal μ A A' 0

def CtZeroC : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ D _ _ A _ =>
  ∀ u, Pc μ (A.J u) = 0 ∧ D.FixedByTypeProjector μ (A.J u) ∧ constantTermL2 μ 1 (A.J u) =ᵐ[μ] 0 ∧ constantTermL2 μ 3 (A.J u) =ᵐ[μ] 0

def ConvRC : Prop := ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A _ => ∀ f : CC K (2 + 2), D.Hecke f → ∃ β, ActsBy μ A f β

def ConvUC : Prop := ForAllC fun K _ _ μ _ μ₂ _ τ₁ τ₂ D d d' A A' =>
  ∀ (σ : K ≃+* K) (θ : Twist μ) (θ₂ : Twist μ₂), UpperTheory.ConvolutionTheory.K.IsGal σ θ → UpperTheory.ConvolutionTheory.K.IsGal σ θ₂ → Stable D θ →
    τ₁.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₂ → τ₂.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₁ →
    ∃ s : Eu d ≃ₗᵢ[ℂ] Eu d', (∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)) ∧
      ∀ (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, v x = s (u x)) → θ.U (A.J u) = A'.J v

def UnitB : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => UnitAt μ A A'

def ProjExC : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' =>
  (∃ P, IsOrthogonalProjectionTwoLines A.J A'.J P) ∧ ∀ T : ℝ, 0 ≤ T → ∃ Λ, IsTrunc A.J A'.J T Λ

def FamilyOf2 : Prop := ForAllC fun _ _ _ μ _ _ _ _ _ _ d _ A A' =>
  TruncCpt μ A A' → ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → ∃ N, Family μ A A' 0 P N d

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
