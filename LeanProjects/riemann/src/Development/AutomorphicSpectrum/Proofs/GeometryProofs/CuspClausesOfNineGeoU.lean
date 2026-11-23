import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.CuspMeanBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTiedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeftStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Field

variable {F : Type} [Field F]

def EffOn (V : Ideal (MRingOver F ι)) (β : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsMultiProjPrime W → V ≤ W →
    ∃ f g, IsRatSection W β f g ∧ ∀ W', 0 ≤ ratDiv W f g W'

end Field

variable {Ω : Type} [Field Ω]

open Classical in

abbrev numQ : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L

theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

section Values

variable {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L} {c : ∀ k, ι k}

def ChartVal (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (s : Ω) (v : L) : Prop :=
  ∃ (e : K → ℕ) (G : MRing ι), IsMultiHomog G e ∧ aeval y G = s * aeval y (GenOnFibres.cmon c e) ∧
    aeval z G = v * aeval z (GenOnFibres.cmon c e)

theorem ChartVal.add {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s + s') (v + v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * GenOnFibres.cmon c e' + GenOnFibres.cmon c e * G',
    GenOnFibres.homog_add (GenOnFibres.homog_mul hG (GenOnFibres.homog_cmon c e'))
      (GenOnFibres.homog_mul (GenOnFibres.homog_cmon c e) hG'), ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h2, h2']; ring

theorem ChartVal.mul {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s * s') (v * v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * G', GenOnFibres.homog_mul hG hG', ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_mul, h2, h2']; ring

end Values

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound

section Systems

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end Systems

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

end Clauses

def FrameFamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ)
    (U : ((Σ k, J k) → ℂ) → ℝ),
    IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → 1 ≤ Dc.j' → 3 * Dc.j' + 1 ≤ Dc.N →
      ∃ (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), S'.IsTied

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
