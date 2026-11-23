import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HermitianSum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LeavesOrthogonalSum

open Complex UpperHalfPlane NumberField Filter Topology
open scoped MatrixGroups Real

noncomputable section

section Character

variable (d : ℕ) [Fact d.Prime]

def chi : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

def Lval (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction (chi d) s

def Lc : ℂ :=
  deriv (Lval d) 1 / Lval d 1

def L0 : ℂ :=
  deriv (Lval d) 0 / Lval d 0

end Character

def phi (τ : ℍ) : ℝ :=
  Real.log (4 * π * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4)

instance fact_no_root (d : ℕ) [Fact d.Prime] : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by
    have hd : (0 : ℚ) < d := by exact_mod_cast (Fact.out : d.Prime).pos
    rw [zero_mul, add_zero] at h
    nlinarith [sq_nonneg r]⟩

abbrev K (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0

instance (d : ℕ) [Fact d.Prime] : NumberField (K d) := {}

section Field

variable (d : ℕ) [Fact d.Prime]

def emb : K d →+* ℂ :=
  (QuadraticAlgebra.lift
    (⟨Complex.I * (Real.sqrt d : ℂ), by
      have h : ((Real.sqrt d : ℝ) : ℂ) * (Real.sqrt d : ℂ) = d := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
        simp
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
      calc Complex.I * (Real.sqrt d : ℂ) * (Complex.I * (Real.sqrt d : ℂ))
          = Complex.I * Complex.I * ((Real.sqrt d : ℂ) * (Real.sqrt d : ℂ)) := by ring
        _ = algebraMap ℚ ℂ (-(d : ℚ)) := by
          rw [h, Complex.I_mul_I]
          simp⟩ :
      {u : ℂ // u * u = (-(d : ℚ)) • 1 + (0 : ℚ) • u}) : K d →ₐ[ℚ] ℂ).toRingHom

def IsTauOf (C : ClassGroup (𝓞 (K d))) (τ : ℍ) : Prop :=
  ∃ (I : ↥(nonZeroDivisors (Ideal (𝓞 (K d))))) (c : ℂ), c ≠ 0 ∧ ClassGroup.mk0 I = C ∧
    (fun a : 𝓞 (K d) ↦ emb d (a : K d)) '' ((I : Ideal (𝓞 (K d))) : Set (𝓞 (K d))) =
      Set.range (fun p : ℤ × ℤ ↦ c * ((p.1 : ℂ) + (p.2 : ℂ) * (τ : ℂ)))

def tauOf (C : ClassGroup (𝓞 (K d))) : ℍ :=
  Classical.epsilon (IsTauOf d C)

def A1 : ℝ :=
  (1 / (classNumber (K d) : ℝ)) * ∑ C : ClassGroup (𝓞 (K d)), phi (tauOf d C)

def partialZeta (C : ClassGroup (𝓞 (K d))) (s : ℂ) : ℂ :=
  ∑' I : {I : ↥(nonZeroDivisors (Ideal (𝓞 (K d)))) // ClassGroup.mk0 I = C},
    ((Ideal.absNorm (I.1 : Ideal (𝓞 (K d))) : ℂ)) ^ (-s)

end Field

def eisTerm (τ : ℍ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  ((τ.im : ℂ)) ^ s / ((‖(p.1 : ℂ) * (τ : ℂ) + p.2‖ : ℝ) : ℂ) ^ (2 * s)

def eis (τ : ℍ) (s : ℂ) : ℂ :=
  ∑' p : {p : ℤ × ℤ // p ≠ 0}, eisTerm τ s p

def rowSum (m : ℤ) (τ : ℍ) (s : ℂ) : ℂ :=
  ∑' n : ℤ, ((‖(m : ℂ) * (τ : ℂ) + n‖ : ℝ) : ℂ) ^ (-2 * s)

def expTwoPiI (x : ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * x)

def freqIntegral (k : ℤ) (Y : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, expTwoPiI (-(k * t)) * (((t ^ 2 + Y ^ 2 : ℝ) : ℂ)) ^ (-s)

def fourierTail (τ : ℍ) (s : ℂ) : ℂ :=
  ((τ.im : ℂ)) ^ s * ∑' m : {m : ℤ // m ≠ 0}, ∑' k : {k : ℤ // k ≠ 0},
    expTwoPiI (k * m * τ.re) * freqIntegral k (|(m : ℝ)| * τ.im) s

section Core

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

@[instance_reducible]
def corePi (h : ∀ i, InnerProductSpace.Core ℂ (V i)) : InnerProductSpace.Core ℂ (∀ i, V i) where
  inner x y := ∑ i, (h i).inner (x i) (y i)
  conj_inner_symm x y := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (h i).conj_inner_symm (x i) (y i)
  re_inner_nonneg x := by
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ ↦ (h i).re_inner_nonneg (x i)
  add_left x y z := by
    simp only [Pi.add_apply, (h _).add_left, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [Pi.smul_apply, (h _).smul_left, Finset.mul_sum]
  definite x hx := by
    have hx' : ∑ i, (h i).inner (x i) (x i) = 0 := hx
    have hre : ∑ i, RCLike.re ((h i).inner (x i) (x i)) = 0 := by
      rw [← map_sum, hx', map_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ (h i).re_inner_nonneg (x i)).1 hre
    funext i
    exact core_eq_zero_of_re (h i) _ (hz i (Finset.mem_univ i))

theorem corePi_inner (h : ∀ i, InnerProductSpace.Core ℂ (V i)) (x y : ∀ i, V i) :
    (corePi h).inner x y = ∑ i, (h i).inner (x i) (y i) := rfl

end Core

section Bundles

open NumberField.ComplexEmbedding TensorProduct ComplexAt

variable {L : Type*} [Field L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Type*) [∀ i, AddCommGroup (E i)]
  [∀ i, Module (𝓞 L) (E i)]

def fibrePi (σ : L →+* ℂ) : Fibre σ (∀ i, E i) ≃ₗ[ℂ] ∀ i, Fibre σ (E i) :=
  (piRight (𝓞 L) (ComplexAt σ) (ComplexAt σ) E).restrictScalars ℂ

variable {E}

theorem fibrePi_conjMap (σ : L →+* ℂ) (x : Fibre σ (∀ i, E i)) (i : ι) :
    fibrePi E (conjugate σ) (conjMap σ (∀ i, E i) x) i = conjMap σ (E i) (fibrePi E σ x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul z v => rfl
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

variable [NumberField L] [∀ i, Module.Finite (𝓞 L) (E i)] [∀ i, Module.Projective (𝓞 L) (E i)]

instance : Module.Projective (𝓞 L) (∀ i, E i) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 L) (M := E))

def orthogonalSum (h : ∀ i, HermitianMetric L (E i)) : HermitianMetric L (∀ i, E i) where
  form σ := coreComap (corePi fun i ↦ (h i).form σ) (fibrePi E σ).toLinearMap
    (fibrePi E σ).injective
  form_conj σ x y := by
    simp only [coreComap_inner, corePi_inner, LinearEquiv.coe_coe, fibrePi_conjMap,
      (h _).form_conj, map_sum]

end Bundles

section Scale

variable {L : Type*} [Field L] [NumberField L] {E : Type*} [AddCommGroup E] [Module (𝓞 L) E]
  [Module.Finite (𝓞 L) E] [Module.Projective (𝓞 L) E]

def scaleForm (h : HermitianMetric L E) (t : ℝ) (ht : 0 < t) : HermitianMetric L E :=
  h.scale (Real.sqrt t) (Real.sqrt_pos.2 ht)

end Scale

def weightedSum {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module (𝓞 L) (E i)]
    [∀ i, Module.Finite (𝓞 L) (E i)] [∀ i, Module.Projective (𝓞 L) (E i)]
    (h : ∀ i, HermitianMetric L (E i)) (vol : ι → ℝ) (hvol : ∀ i, 0 < vol i) :
    HermitianMetric L (∀ i, E i) :=
  orthogonalSum fun i ↦ scaleForm (h i) (vol i / ∑ j, vol j)
    (div_pos (hvol i) (Finset.sum_pos (fun j _ ↦ hvol j) ⟨i, Finset.mem_univ i⟩))

def ChiFacts.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (chi d).IsPrimitive ∧ chi d (-1) = -1 ∧ ∀ a : ZMod d, (chi d a).im = 0

def CompletedForm.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ s : ℂ, (∀ n : ℕ, s ≠ -(2 * (n : ℂ) + 1)) →
    (d : ℂ) ^ ((s + 1) / 2) * DirichletCharacter.completedLFunction (chi d) s =
      ((d : ℂ) / π) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * Lval d s

def LNonzero.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → Lval d 1 ≠ 0 ∧ Lval d 0 ≠ 0

def LogDerivRelation.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (1 / 2 : ℂ) * (Real.log (d / π) : ℂ) + (1 / 2) * digamma (1 / 2) + L0 d =
      -((1 / 2 : ℂ) * (Real.log (d / π) : ℂ) + (1 / 2) * digamma 1 + Lc d)

def LeafFE.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    L0 d = -Lc d - (Real.log (d / π) : ℂ) + (Real.eulerMascheroniConstant : ℂ) + (Real.log 2 : ℂ)

def PhiInvariant.Statement : Prop :=
  ∀ (g : SL(2, ℤ)) (τ : ℍ), phi (g • τ) = phi τ

def TauExists.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ C : ClassGroup (𝓞 (K d)),
    (∃ τ : ℍ, IsTauOf d C τ) ∧ ∀ τ τ' : ℍ, IsTauOf d C τ → IsTauOf d C τ' → phi τ = phi τ'

def EisSummable.Statement : Prop :=
  ∀ τ : ℍ,
    (∀ s : ℂ, 1 < s.re → Summable fun p : {p : ℤ × ℤ // p ≠ 0} ↦ ‖eisTerm τ s p‖) ∧
    TendstoLocallyUniformlyOn
      (fun (S : Finset {p : ℤ × ℤ // p ≠ 0}) (s : ℂ) ↦ ∑ p ∈ S, eisTerm τ s p)
      (eis τ) atTop {s : ℂ | 1 < s.re} ∧
    AnalyticOnNhd ℂ (eis τ) {s : ℂ | 1 < s.re}

def EisRows.Statement : Prop :=
  ∀ (τ : ℍ) (s : ℂ), 1 < s.re →
    eis τ s = 2 * riemannZeta (2 * s) * (τ.im : ℂ) ^ s +
      (τ.im : ℂ) ^ s * ∑' m : {m : ℤ // m ≠ 0}, rowSum m τ s

def RowPoisson.Statement : Prop :=
  ∀ (τ : ℍ) (m : ℤ), m ≠ 0 → ∀ s : ℂ, 1 / 2 < s.re →
    rowSum m τ s = ∑' k : ℤ, expTwoPiI (k * m * τ.re) * freqIntegral k (|(m : ℝ)| * τ.im) s

def ZeroFrequency.Statement : Prop :=
  ∀ Y : ℝ, 0 < Y → ∀ s : ℂ, 1 / 2 < s.re →
    freqIntegral 0 Y s =
      (Real.sqrt π : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s * (Y : ℂ) ^ (1 - 2 * s)

def NonzeroFrequencyBound.Statement : Prop :=
  ∃ F : ℤ → ℝ → ℂ → ℂ,
    (∀ k : ℤ, k ≠ 0 → ∀ Y : ℝ, 0 < Y →
      Differentiable ℂ (F k Y) ∧ ∀ s : ℂ, 1 / 2 < s.re → F k Y s = freqIntegral k Y s) ∧
    ∀ y₀ : ℝ, 0 < y₀ → ∃ ε > 0, ∃ C : ℝ, ∀ k : ℤ, k ≠ 0 → ∀ Y : ℝ, y₀ ≤ Y → ∀ s : ℂ,
      ‖s - 1‖ < ε → ‖F k Y s‖ ≤ C * Real.exp (-π * |(k : ℝ)| * Y) * Y ^ (1 - 2 * s.re)

def NonzeroFrequencyValue.Statement : Prop :=
  ∀ (k : ℤ) (Y : ℝ), 0 < Y →
    freqIntegral k Y 1 = ((π / Y * Real.exp (-2 * π * |(k : ℝ)| * Y) : ℝ) : ℂ)

def EisExpansion.Statement : Prop :=
  ∀ τ : ℍ,
    (∀ s : ℂ, 1 < s.re →
      eis τ s = 2 * riemannZeta (2 * s) * (τ.im : ℂ) ^ s +
        2 * (Real.sqrt π : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s *
          riemannZeta (2 * s - 1) * (τ.im : ℂ) ^ (1 - s) + fourierTail τ s) ∧
    AnalyticAt ℂ (fourierTail τ) 1

def BValue.Statement : Prop :=
  ∀ τ : ℍ,
    fourierTail τ 1 = ((-2 * π * Real.log
      (‖∏' n : ℕ, (1 - Complex.exp (2 * π * Complex.I * (τ : ℂ)) ^ (n + 1))‖ ^ 2) : ℝ) : ℂ)

def KroneckerFirstLimit.Statement : Prop :=
  ∀ τ : ℍ, ∃ f : ℂ → ℂ, AnalyticAt ℂ f 1 ∧
    (∀ᶠ s in 𝓝 1, 1 < s.re → eis τ s - π / (s - 1) = f s) ∧
    f 1 = ((2 * π * (Real.eulerMascheroniConstant - Real.log 2 -
      Real.log (Real.sqrt τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 2)) : ℝ) : ℂ)

def PartialZetaEis.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ (C : ClassGroup (𝓞 (K d))) (τ : ℍ),
    IsTauOf d C⁻¹ τ → ∀ s : ℂ, 1 < s.re →
      partialZeta d C s =
        1 / (Units.torsionOrder (K d) : ℂ) * ((2 / Real.sqrt d : ℝ) : ℂ) ^ s * eis τ s

def ZetaFactor.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (∀ s : ℂ, 1 < s.re → dedekindZeta (K d) s = riemannZeta s * Lval d s) ∧
    Tendsto (fun s : ℂ ↦ dedekindZeta (K d) s - Lval d 1 / (s - 1))
      (𝓝[{s : ℂ | 1 < s.re}] 1) (𝓝 (Lval d 1 * (Real.eulerMascheroniConstant + Lc d)))

def ClassNumberL.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    ((2 * π * classNumber (K d) / (Units.torsionOrder (K d) * Real.sqrt d) : ℝ) : ℂ) = Lval d 1

def ClassMeanIdentity.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (A1 d : ℂ) = (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * π / Real.sqrt d) : ℂ) - Lc d

def LeafKL.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → (A1 d : ℂ) = L0 d + (1 / 2) * (Real.log d : ℂ)

def OrthogonalDegree.Statement.{u, v, w} : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (E : ι → Type w) [∀ i, AddCommGroup (E i)] [∀ i, Module (𝓞 L) (E i)]
    [∀ i, Module.Finite (𝓞 L) (E i)] [∀ i, Module.Projective (𝓞 L) (E i)]
    (h : ∀ i, HermitianMetric L (E i)),
    arithDegree (orthogonalSum h) = ∑ i, arithDegree (h i)

def ScaleDegree.Statement.{u, w} : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L] (E : Type w) [AddCommGroup E] [Module (𝓞 L) E]
    [Module.Finite (𝓞 L) E] [Module.Projective (𝓞 L) E] (h : HermitianMetric L E) (t : ℝ)
    (ht : 0 < t),
    arithDegree (scaleForm h t ht) =
      arithDegree h - (1 / 2) * Module.finrank ℚ L * Module.finrank (𝓞 L) E * Real.log t

def SumWeights.Statement.{u, v, w} : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (E : ι → Type w) [∀ i, AddCommGroup (E i)] [∀ i, Module (𝓞 L) (E i)]
    [∀ i, Module.Finite (𝓞 L) (E i)] [∀ i, Module.Projective (𝓞 L) (E i)]
    (h : ∀ i, HermitianMetric L (E i)) (vol : ι → ℝ) (hvol : ∀ i, 0 < vol i),
    arithDegree (weightedSum h vol hvol) / Module.finrank ℚ L =
        ∑ i, arithDegree (h i) / Module.finrank ℚ L +
          (1 / 2) * ∑ i, (Module.finrank (𝓞 L) (E i) : ℝ) * Real.log ((∑ j, vol j) / vol i) ∧
      ∑ i, arithDegree (h i) / Module.finrank ℚ L ≤
        arithDegree (weightedSum h vol hvol) / Module.finrank ℚ L

def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), Real.log p / p ≤ Real.log x + C

end

end GroundTheory.Heights₂.Heights.LeavesOrthogonalSum
