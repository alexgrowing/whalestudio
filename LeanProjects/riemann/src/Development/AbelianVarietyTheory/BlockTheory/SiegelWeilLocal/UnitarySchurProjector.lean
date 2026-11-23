import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.SmoothOnGVIff

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality

section Defs

variable {G : Type} [Group G]
variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsUnitaryRep [TopologicalSpace G] (π : G → (H →L[ℂ] H)) : Prop :=
  π 1 = ContinuousLinearMap.id ℂ H ∧ (∀ a b, π (a * b) = (π a).comp (π b)) ∧
    (∀ g v, ‖π g v‖ = ‖v‖) ∧ ∀ v, Continuous fun g => π g v

def IsTopIrred (σ : G → (Hs →L[ℂ] Hs)) : Prop :=
  ∀ S : Submodule ℂ Hs, IsClosed (S : Set Hs) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤

def SchurOrthogonality [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ u v u' v' : Hs,
    Integrable (fun g => ⟪v, σ g u⟫_ℂ * star ⟪v', σ g u'⟫_ℂ) μ ∧
    ∫ g, ⟪v, σ g u⟫_ℂ * star ⟪v', σ g u'⟫_ℂ ∂μ = (d : ℂ)⁻¹ * ⟪u', u⟫_ℂ * star ⟪v', v⟫_ℂ

def diagCoef (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (g : G) : ℂ := ⟪w, σ g w⟫_ℂ

def testFn (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) (g : G) : ℂ := (d : ℂ) * star (diagCoef σ w g)

def IsIntegratedOp [MeasurableSpace G] (μ : Measure G) (π : G → (H →L[ℂ] H)) (f : G → ℂ)
    (P : H →L[ℂ] H) : Prop :=
  Integrable f μ ∧ ∀ x y : H, ⟪x, P y⟫_ℂ = ∫ g, f g * ⟪x, π g y⟫_ℂ ∂μ

def ketBra (w : Hs) : Hs →L[ℂ] Hs := (innerSL ℂ w).smulRight w

def intertwiners (σ : G → (Hs →L[ℂ] Hs)) (π : G → (H →L[ℂ] H)) : Submodule ℂ (Hs →L[ℂ] H) where
  carrier := {T | ∀ g, T.comp (σ g) = (π g).comp T}
  add_mem' := by
    intro a b ha hb g
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c a ha g
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ha g]

def evalIntertwiner (σ : G → (Hs →L[ℂ] Hs)) (π : G → (H →L[ℂ] H)) (w : Hs) :
    intertwiners σ π →ₗ[ℂ] H where
  toFun T := (T : Hs →L[ℂ] H) w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SchurRelations [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) :
    Prop :=
  (∀ g, star (testFn σ d w g⁻¹) = testFn σ d w g) ∧
    (∀ y, Integrable (fun g => testFn σ d w g * testFn σ d w (g⁻¹ * y)) μ ∧
      ∫ g, testFn σ d w g * testFn σ d w (g⁻¹ * y) ∂μ = testFn σ d w y) ∧
    (∀ x y, Integrable (fun g => testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y) ∂μ = diagCoef σ w x * testFn σ d w y) ∧
    IsIntegratedOp μ σ (testFn σ d w) (ketBra w)

def ProjectorProps (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (π : G → (H →L[ℂ] H)) (P : H →L[ℂ] H) : Prop :=
  P.comp P = P ∧ (∀ x y : H, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ) ∧
    (∀ x, P.comp ((π x).comp P) = diagCoef σ w x • P) ∧
    Function.Injective (evalIntertwiner σ π w) ∧
    LinearMap.range (evalIntertwiner σ π w) = LinearMap.range (P : H →ₗ[ℂ] H)

def ProjectorStatement [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G → (H →L[ℂ] H)), IsUnitaryRep π →
    (∃ P, IsIntegratedOp μ π (testFn σ d w) P) ∧
      ∀ P, IsIntegratedOp μ π (testFn σ d w) P → ProjectorProps σ w π P

end Defs

def AbstractSchurProjector : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    IsUnitaryRep σ → IsTopIrred σ → SchurOrthogonality μ σ d → ‖w‖ = 1 →
    Integrable (testFn σ d w) μ →
    SchurRelations μ σ d w ∧ ProjectorStatement μ σ d w

def realRank {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card

def UnitarySchurProjectorUnder (gap : ∀ n : ℕ, (Fin n → Bool) → (Fin n → ℝ) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    Formalism.QuantumDeterminants.IsHCParam lam → gap n ε lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsLowUnit ε lam σ w →
    Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) σ d →
    SchurRelations (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d w ∧
      ProjectorStatement (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d w

def UnitarySchurProjector : Prop :=
  UnitarySchurProjectorUnder fun n ε lam =>
    Formalism.QuantumDeterminants.GapAtLeast ε lam (120 * (n : ℝ) * (realRank ε : ℝ) ^ (3 / 2 : ℝ))

def UnitarySchurProjectorSharp : Prop :=
  UnitarySchurProjectorUnder fun n ε lam =>
    ∀ a b : Fin n, ε a ≠ ε b → 16 * (n : ℝ) * (realRank ε : ℝ) ^ (3 / 2 : ℝ) < |lam a - lam b|

def SchurProjector : Prop := AbstractSchurProjector ∧ UnitarySchurProjector

example {n : ℕ} (ε : Fin n → Bool) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (d : ℝ) (μ : Measure (Formalism.REAL.UJ ε)) :
    SchurOrthogonality μ (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d ↔ Formalism.MainNotions.S.IsFdeg μ σ d := by
  unfold SchurOrthogonality Formalism.MainNotions.S.IsFdeg Formalism.MainNotions.S.coefOn
  refine and_congr Iff.rfl (forall_congr' fun u => forall_congr' fun v => forall_congr' fun u' =>
    forall_congr' fun v' => and_congr Iff.rfl ?_)
  have : (d : ℂ)⁻¹ * ⟪u', u⟫_ℂ * star ⟪v', v⟫_ℂ = ⟪u', u⟫_ℂ * ⟪v, v'⟫_ℂ / (d : ℂ) := by
    rw [← inner_conj_symm v v', div_eq_mul_inv]
    simp only [RCLike.star_def]
    ring
  rw [this]

example {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (w u : Hs) :
    ketBra w u = ⟪w, u⟫_ℂ • w := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality
