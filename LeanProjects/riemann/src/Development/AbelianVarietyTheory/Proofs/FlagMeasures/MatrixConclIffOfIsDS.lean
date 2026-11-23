import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.UnitarySchurProjector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SchurProjCompare

section Abstract

variable {G : Type} [Group G]
variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCyclic (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) : Prop :=
  Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set Hs)

omit [Group G] in

theorem IsCyclic.ext {σ : G → (Hs →L[ℂ] Hs)} {w : Hs} (h : IsCyclic σ w) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {A B : Hs →L[ℂ] E}
    (hAB : ∀ g, A (σ g w) = B (σ g w)) : A = B :=
  ContinuousLinearMap.ext_on h (by rintro _ ⟨g, rfl⟩; exact hAB g)

def IsometricProps [CompleteSpace H] (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (π : G → (H →L[ℂ] H))
    (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧
    (∀ x : G, P ∘L π x ∘L P = ⟪w, σ x w⟫_ℂ • P) ∧
    (∀ v ∈ LinearMap.range (P : H →ₗ[ℂ] H), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : Hs →ₗᵢ[ℂ] H, io w = v ∧ ∀ (g : G) (u : Hs), io (σ g u) = π g (io u)) ∧
    ((LinearMap.range (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) =
      {v | ∃ io : Hs →L[ℂ] H, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w}

def IsometricConcl [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs))
    (d : ℝ) (w : Hs) : Prop :=
  (∀ g : G, star (testFn σ d w g⁻¹) = testFn σ d w g) ∧
    (∀ x y : G, ∫ g, testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * testFn σ d w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : G → (Hp →L[ℂ] Hp)), IsUnitaryRep π →
      (∃ P, IsIntegratedOp μ π (testFn σ d w) P) ∧
        ∀ P, IsIntegratedOp μ π (testFn σ d w) P → IsometricProps σ w π P

def homOfRep [TopologicalSpace G] (π : G → (H →L[ℂ] H)) (hπ : IsUnitaryRep π) : G →* (H →L[ℂ] H) where
  toFun := π
  map_one' := hπ.1
  map_mul' := hπ.2.1

def NormHyp [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ)
    (w : Hs) : Prop :=
  (∀ g x, ‖σ g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => σ g x) ∧ 0 < d ∧
    (∀ x y : Hs, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) ∧
    ‖w‖ = 1 ∧ Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ

def HomConcl [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ)
    (w : Hs) : Prop :=
  (∀ g : G, star (phA d σ w g⁻¹) = phA d σ w g) ∧
    (∀ x y : G, ∫ g, phA d σ w g * phA d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phA d σ w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) →
      (∃ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P) ∧
      ∀ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P → IsometricProps σ w π P

def FirstAt [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs), NormHyp μ σ d w → HomConcl μ σ d w

def SecondAt [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    IsUnitaryRep σ → IsTopIrred σ → SchurOrthogonality μ σ d → ‖w‖ = 1 →
    Integrable (testFn σ d w) μ → SchurRelations μ σ d w ∧ ProjectorStatement μ σ d w

end Abstract

section Unitary

open Matrix Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def toGroup (M : UJset ε) : UJ ε :=
  have h : Jm ε * M.1ᴴ * Jm ε * M.1 = 1 := by
    have h0 : M.1ᴴ * Jm ε * M.1 = Jm ε := M.2
    rw [Matrix.mul_assoc (Jm ε), Matrix.mul_assoc (Jm ε), h0, Jm_mul_self]
  ⟨⟨M.1, Jm ε * M.1ᴴ * Jm ε, mul_eq_one_comm.1 h, h⟩, M.2⟩

theorem continuous_toGroup : Continuous (toGroup (ε := ε)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩) _
  exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
    continuous_const

theorem toGroup_umat (g : UJ ε) : toGroup ⟨umat g, g.2⟩ = g := Subtype.ext (Units.ext rfl)

open Classical in

def onMatrices (π : UJ ε → (H →L[ℂ] H)) (M : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  if h : M ∈ UJset ε then π (toGroup ⟨M, h⟩) else 0

theorem onMatrices_umat (π : UJ ε → (H →L[ℂ] H)) (g : UJ ε) : onMatrices π (umat g) = π g := by
  have h : umat g ∈ UJset ε := g.2
  rw [onMatrices, dif_pos h, toGroup_umat]

theorem isURepOn_iff (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsURepOn (UJset ε) π ↔ IsUnitaryRep fun g : UJ ε => π (umat g) := by
  constructor
  · intro h
    have hc : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
    exact ⟨h.1.1, fun a b => h.1.2 (umat a) a.2 (umat b) b.2, fun g => h.2.1 (umat g) g.2,
      fun v => (h.2.2 v).comp_continuous hc fun g => g.2⟩
  · intro h
    refine ⟨⟨h.1, fun a ha b hb => h.2.1 (toGroup ⟨a, ha⟩) (toGroup ⟨b, hb⟩)⟩,
      fun g hg => h.2.2.1 (toGroup ⟨g, hg⟩), fun v => ?_⟩
    rw [continuousOn_iff_continuous_domRestrict]
    exact (h.2.2.2 v).comp continuous_toGroup

def MatrixConcl (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  Integrable (phLoc ε σ w) (muG ε) ∧
    (∀ g : UJ ε, star (phLoc ε σ w g⁻¹) = phLoc ε σ w g) ∧
    (∀ x y : UJ ε, ∫ g, phLoc ε σ w g * phLoc ε σ w (x⁻¹ * g⁻¹ * y) ∂(muG ε) =
      coefOn σ w w x * phLoc ε σ w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : Matrix (Fin n) (Fin n) ℂ → (Hp →L[ℂ] Hp)), IsURepOn (UJset ε) π →
      (∃ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P) ∧
      ∀ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P →
        IsometricProps (fun g : UJ ε => σ (umat g)) w (fun g : UJ ε => π (umat g)) P

end Unitary

def FirstLocallyCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], FirstAt μ

def SecondAllGroups : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    SecondAt μ

end GlobalTheory.SchurProjCompare
