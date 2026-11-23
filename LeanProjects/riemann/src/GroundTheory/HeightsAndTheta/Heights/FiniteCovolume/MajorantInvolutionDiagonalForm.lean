import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section MatrixLevel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsMajorantOf (H P : Matrix ι ι ℂ) : Prop :=
  P.PosDef ∧ H.IsHermitian ∧ IsUnit H.det ∧ P * H⁻¹ * P = H

def majInvolution (H P : Matrix ι ι ℂ) : Matrix ι ι ℂ := H⁻¹ * P

def plusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z + majInvolution H P *ᵥ z)

def minusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z - majInvolution H P *ᵥ z)

def pReflection (P : Matrix ι ι ℂ) (v : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (2 / (star v ⬝ᵥ (P *ᵥ v))) • (vecMulVec v (star v) * P)

def phaseOnMinus (H P : Matrix ι ι ℂ) (c : ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (1 + majInvolution H P) + (c / 2) • (1 - majInvolution H P)

variable (ι)

def MajorantBound.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ,
    ‖star z ⬝ᵥ (H *ᵥ z)‖ ≤ (star z ⬝ᵥ (P *ᵥ z)).re

def EigenspacesOrthogonal.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ a b : ι → ℂ,
    majInvolution H P *ᵥ a = a → majInvolution H P *ᵥ b = -b → star a ⬝ᵥ (P *ᵥ b) = 0

def IsotropicSplit.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ, star z ⬝ᵥ (H *ᵥ z) = 0 →
    majInvolution H P *ᵥ plusPart H P z = plusPart H P z ∧
    majInvolution H P *ᵥ minusPart H P z = -minusPart H P z ∧
    star (plusPart H P z) ⬝ᵥ (P *ᵥ plusPart H P z) =
      star (minusPart H P z) ⬝ᵥ (P *ᵥ minusPart H P z)

def EigenReflection.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ v : ι → ℂ, v ≠ 0 →
    majInvolution H P *ᵥ v = ε • v →
    (pReflection P v)ᴴ * P * pReflection P v = P ∧ (pReflection P v)ᴴ * H * pReflection P v = H ∧
      pReflection P v *ᵥ v = -v ∧ ∀ u : ι → ℂ, star v ⬝ᵥ (P *ᵥ u) = 0 → pReflection P v *ᵥ u = u

def EigenReflectionMaps.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ a a' : ι → ℂ,
    majInvolution H P *ᵥ a = ε • a → majInvolution H P *ᵥ a' = ε • a' →
    star a ⬝ᵥ (P *ᵥ a) = star a' ⬝ᵥ (P *ᵥ a') →
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∃ R : Matrix ι ι ℂ, Rᴴ * P * R = P ∧ Rᴴ * H * R = H ∧ R *ᵥ a' = α • a ∧
      ∀ u : ι → ℂ, majInvolution H P *ᵥ u = (-ε) • u → R *ᵥ u = u

def PhaseOnMinus.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ c : ℂ, ‖c‖ = 1 →
    (phaseOnMinus H P c)ᴴ * P * phaseOnMinus H P c = P ∧
      (phaseOnMinus H P c)ᴴ * H * phaseOnMinus H P c = H ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = u → phaseOnMinus H P c *ᵥ u = u) ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = -u → phaseOnMinus H P c *ᵥ u = c • u)

def KTransitive.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z z' : ι → ℂ, z ≠ 0 → z' ≠ 0 →
    star z ⬝ᵥ (H *ᵥ z) = 0 → star z' ⬝ᵥ (H *ᵥ z') = 0 →
    ∃ k : GL ι ℂ, k ∈ unitaryGroupMatrix (starRingEnd ℂ) H ∧
      k ∈ unitaryGroupMatrix (starRingEnd ℂ) P ∧ ∃ c : ℂ, (k : Matrix ι ι ℂ) *ᵥ z' = c • z

end MatrixLevel

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermAtPlace.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (w : InfinitePlace E) (x y : W),
    w.embedding (h.toSesq x y) = star (vecAt v x w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v y w)

def GramAtData.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ w : InfinitePlace E, (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det

def ArchInvariant.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (g : archUnitary h v) (y z : InfinitePlace E → ι → ℂ) (w : InfinitePlace E),
    star (invApply g y w) ⬝ᵥ (gramAt h v w *ᵥ invApply g z w) =
      star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)

def LenSq.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (y : InfinitePlace E → ι → ℂ),
    (∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re) ∧
      M.len y ^ 2 = ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re

def VecAtNeZero.Statement (v : Basis ι E W) : Prop :=
  ∀ x : W, x ≠ 0 → ∀ w : InfinitePlace E, vecAt v x w ≠ 0

variable (E) in

def IntegerSmallAtPlaces.Statement : Prop :=
  ∀ a ∈ integralClosure ℤ E, (∀ w : InfinitePlace E, w a < 1) → a = 0

end Places

section Line

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W]

variable (E) in

def intSubgroup : AddSubgroup E := (algebraMap (𝓞 E) E).toAddMonoidHom.range

def lineCoeffs (La : AddSubgroup W) (x : W) : AddSubgroup E :=
  La.comap ((smulAddHom E W).flip x)

def weightedEmbed (c : InfinitePlace E → ℝ) : E →+ EuclideanSpace ℝ (InfinitePlace E × Fin 2) where
  toFun a := WithLp.toLp 2 fun p =>
    Real.sqrt (c p.1) * (if p.2 = 0 then (p.1.embedding a).re else (p.1.embedding a).im)
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp only [map_add, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> ring

variable (W) in

def LineIndexCoeffs.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), x ≠ 0 →
    lineIndex E La x = (intSubgroup E).relIndex (lineCoeffs La x)

variable (W) in

def LineCoeffsFG.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), La.FG → x ≠ 0 → (lineCoeffs (E := E) La x).FG

variable (E)

def CoeffLatticeBasis.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG → Nonempty (Basis (Fin (finrank ℚ E)) ℤ A)

def IndexLeDet.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → ∀ (e : Basis (Fin (finrank ℚ E)) ℤ A)
    (a : Fin (finrank ℚ E) → 𝓞 E) (T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ),
    LinearIndependent ℚ (fun i => (a i : E)) → (∀ i, (a i : E) = ∑ j, T i j • (e j : E)) →
    ((intSubgroup E).relIndex A : ℝ) ≤ |(T.det : ℝ)|

def WeightedNormSq.Statement : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 ≤ c w) → ∀ a : E,
    ‖weightedEmbed c a‖ ^ 2 = ∑ w, c w * ‖w.embedding a‖ ^ 2

def WeightedSpaceDim.Statement [IsTotallyComplex E] : Prop :=
  finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E

def WeightedIndexBound.Statement [IsTotallyComplex E] : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 < c w) → ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG →
    (∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) →
    ∀ r : ℝ, (∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ((intSubgroup E).relIndex A : ℝ) ≤ (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E

end Line

section Minkowski

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

def MinkowskiVolumeForm.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ), 0 < lam →
    (∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
    (lam / Real.sqrt d) ^ d ≤ |o.volumeForm b|

def VolumeFormIntComb.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (T : Matrix (Fin d) (Fin d) ℤ),
    o.volumeForm (fun i => ∑ j, (T i j : ℝ) • b j) = (T.det : ℝ) * o.volumeForm b

end Minkowski

section Steps

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def WeightedLenSmul.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W) (a : E),
    M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, ‖w.embedding a‖ ^ 2 *
        (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

def WeightPos.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W), x ≠ 0 → ∀ w : InfinitePlace E,
    0 < (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

end Steps

section Inhabitants

open GaussianPlane

def H0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

def z0 : Fin 2 → ℂ := fun _ => 1

def e1 : Fin 2 → ℂ := Pi.single 0 1

def e2 : Fin 2 → ℂ := Pi.single 1 1

theorem card_chooseBasisIndex_Eg :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 Eg)) = finrank ℚ Eg := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

def intBasisG : Basis (Fin (finrank ℚ Eg)) ℤ (𝓞 Eg) :=
  (RingOfIntegers.basis Eg).reindex (Fintype.equivFinOfCardEq card_chooseBasisIndex_Eg)

def intSubgroupEquiv (K : Type*) [Field K] [NumberField K] : 𝓞 K ≃ₗ[ℤ] intSubgroup K :=
  (AddMonoidHom.ofInjective (f := (algebraMap (𝓞 K) K).toAddMonoidHom)
    (FaithfulSMul.algebraMap_injective (𝓞 K) K)).toIntLinearEquiv

def intSubgroupBasisG : Basis (Fin (finrank ℚ Eg)) ℤ (intSubgroup Eg) :=
  intBasisG.map (intSubgroupEquiv Eg)

instance fact_finrank_euclidean_fin_one : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
