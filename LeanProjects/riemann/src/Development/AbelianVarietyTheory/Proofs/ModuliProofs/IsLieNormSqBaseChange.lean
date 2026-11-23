import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialEtaPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieNormSqIffEqPiDivCovolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CurveHomExtOfDerivativeLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory.CMPeriodCompare

section Analytic

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)}
    (he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ X} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e (L w) v) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => e (L z)) w v := by
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  refine ⟨by simpa using h0, fun U hU f => ?_⟩
  rw [h1 U hU f]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← h0]
    intro x _
    exact hU (by trivial)
  have hd := _root_.GlobalTheory.LocalLift.hol_differentiableAt he (Set.mem_univ 0) hU0 f
  unfold _root_.GlobalTheory.FibreDeriv.jet
  simp only [map_zero]
  congr 2
  have hd' : DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f)
      (LinearMap.toContinuousLinearMap L 0) := by
    simpa using hd
  have hc := hd'.hasFDerivAt.comp (0 : Fin g' → ℂ) (LinearMap.toContinuousLinearMap L).hasFDerivAt
  rw [show (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e (L z)) U f) =
      (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L) from rfl, hc.fderiv]
  simp

variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in
private theorem isDerivAt0_ex_of_isDiff_tangent (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g)
    {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (u.ex z).left) w t.left := by
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left = (u.ex 0).left := by
    rw [_root_.GlobalTheory.TangentOrigin.ex_zero_left]
    exact ht
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff]
  refine ⟨h0, fun U h f => ?_⟩
  ext
  · rw [_root_.GlobalTheory.FibreDeriv.fst_evEps _ _ h0, _root_.GlobalTheory.FibreDeriv.fst_jet]
  · have := hw U h f
    unfold _root_.GlobalTheory.FibreDeriv.jet
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [← this]
    rfl

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in

theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_line (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A}
    (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (g := 1) (fun z => (u.ex (z 0 • w)).left ≫ φ) (fun _ => 1) (t.left ≫ φ) := by
  have hu := isDerivAt0_ex_of_isDiff_tangent u ht hw
  have he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => (u.ex z).left) := by
    simpa using _root_.GlobalTheory.HomLinear.isHolTo_ex_comp u (𝟙 _)
  let L : (Fin 1 → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) := (LinearMap.proj 0).smulRight w
  have hL : L (fun _ => 1) = w := by simp [L]
  rw [← hL] at hu
  exact _root_.GlobalTheory.FibreDeriv.isDerivAt0_comp (_root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear he L hu) φ

variable {v : epsR R ⟶ P.A}

variable {ex : ℂ → (Over.mk (spMap s) ⟶ P.A)} {Λ : Submodule ℤ ℂ}

end Analytic

section Arithmetic

variable {K : Type} [Field K] [NumberField K]

end Arithmetic

section Data

variable (d : ℕ) (K : Type) [Field K] [NumberField K] {M : Type} [Field M] [NumberField M]

def PolData (s₀ : M →+* ℂ) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) : Prop :=
  s₀ w = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
  (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
    IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
    IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
  (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
    IsPolFibre (s₀.comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * s₀ w)) ∧
  (∀ s : M →+* ℂ, ∃ r : ℝ, 0 < r ∧ ∀ r', IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r' ↔ r' = r) ∧
  ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) →
  ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
    (∑ s, Real.log (n s)) / Module.finrank ℚ M =
      (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K

def HasPolCurve : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
    PolData d K (algebraMap M ℂ) w P v

variable {d K}

def ExpData (io : K →+* ℂ) (s₀ : M →+* ℂ) (A : Over (Sp (𝓞 M))) [GrpObj A] (D : epsR (𝓞 M) ⟶ A) : Prop :=
  ∃ (j : 𝓞 K →+* 𝓞 M) (act : OAct (𝓞 K) A)
    (ex : ∀ s : M →+* ℂ, ℂ → (Over.mk (spMap (s.comp (algebraMap (𝓞 M) M))) ⟶ A))
    (Λ : (M →+* ℂ) → Submodule ℤ ℂ),
    (∀ a : 𝓞 K, s₀ (j a : M) = io (a : K)) ∧
    IsAbelianScheme A ∧
    IsLieBasis (fun _ : Fin 1 => D) ∧
    (∀ a : 𝓞 K, (D ≫ act.act a).left = spMap (epsScaleR (j a)) ≫ D.left) ∧
    (∀ s, IsExponential A D (s.comp (algebraMap (𝓞 M) M)) (ex s) (Λ s)) ∧
    (∀ (s : M →+* ℂ) (a : 𝓞 K) (z : ℂ), ex s (s (j a : M) * z) = ex s z ≫ act.act a) ∧
    (∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ, z ∈ Λ s₀ ↔ ∃ a : 𝓞 K, z = c * io (a : K)) ∧
    (∃ τ : ClassGroup (𝓞 K) → ℍ, ∀ C, IsClassPoint io C (τ C)) ∧
    ∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ C, IsClassPoint io C (τ C)) →
      (∑ s : M →+* ℂ, Real.log (sqLen (Λ s) 1)) / (Module.finrank ℚ M : ℝ) =
        -((∑ C, Real.log (etaPeriod (τ C))) / (classNumber K : ℝ))

end Data

section Main

def Polarisable {S : Scheme.{0}} (A : Over S) [GrpObj A] : Prop :=
  ∃ (g : ℕ) (L : LB A.left), SmoothOfRelativeDimension g A.hom ∧ L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧
    Out.RelAmple A L ∧ Out.KTriv A L

variable {d : ℕ} {K : Type} [Field K] [NumberField K]

def HasPolarisableExp (io : K →+* ℂ) : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : NumberField M) (s₀ : M →+* ℂ) (A : Over (Sp (𝓞 M))) (_ : GrpObj A)
    (D : epsR (𝓞 M) ⟶ A), Polarisable A ∧ ExpData io s₀ A D

end Main

end GlobalTheory.CMPeriodCompare
