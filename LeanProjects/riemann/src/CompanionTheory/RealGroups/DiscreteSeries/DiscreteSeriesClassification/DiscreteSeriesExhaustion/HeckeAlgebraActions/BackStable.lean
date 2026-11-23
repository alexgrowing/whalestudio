import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC)

variable {n : ℕ}

def cn (n : ℕ) : ℂ := ((n : ℂ) - 1) / 2

def QdetEq : Prop :=
  ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ),
    qdet E x = capelliC E x

def minorOp {m : ℕ} (X : GMod (m + 1)) (x : ℂ) : Module.End ℂ (Fin (m + 1) → X.V) where
  toFun f := fun d => ∑ b : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (b : ℕ))) • cminor X.E d.succAbove b.succAbove x (f b)
  map_add' f g := by funext d; simp [smul_add, sum_add_distrib]
  map_smul' c f := by funext d; simp [smul_sum, smul_comm c]

def RankOne : Prop :=
  ∀ (m : ℕ) (X : GMod (m + 1)) (x : ℂ),
    qdet (tensE X) x = (qdet X.E x).compLeft (Fin (m + 1)) + minorOp X (x - 1)

def OmMinor : Prop :=
  ∀ (m : ℕ) (X : GMod (m + 1)) (x : ℂ),
    (x • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) * minorOp X (x - 1) = (qdet X.E x).compLeft (Fin (m + 1))

def QdetTens : Prop :=
  ∀ (n : ℕ) (X : GMod n) (u : ℂ),
    qdet (tensE X) u * (u • (1 : Module.End ℂ (Fin n → X.V)) + om X) =
      (qdet X.E u).compLeft (Fin n) * ((u + 1) • (1 : Module.End ℂ (Fin n → X.V)) + om X)

def CayleyHam : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ), HasChar X χ →
    ∃ K : ℕ, ((List.ofFn fun t : Fin n => om X - (χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))).prod) ^ K = 0

def NonVan : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), HasChar X χ → Nontrivial X.V → (∀ r, χ r ≠ χ s + 1) →
    stepSub X (χ s) ≠ ⊥

def NonScal : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), ScalChar X χ → Nontrivial X.V → (∀ r, χ r ≠ χ s + 1) →
    (∃ r, r ≠ s ∧ χ r = χ s) → ∃ f ∈ stepSub X (χ s), om X f ≠ (χ s - cn n) • f

def Back : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), HasChar X χ → (∀ r, χ r ≠ χ s + 1) →
    ScalChar (step X (χ s)) (χ + Pi.single s 1) →
      ScalChar X χ ∧ ∀ f ∈ stepSub X (χ s), om X f = (χ s - cn n) • f

def FwdSimple : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), IsSimple X → ScalChar X χ → (∀ r, χ r ≠ χ s + 1) →
    (∀ r, r ≠ s → χ r ≠ χ s) → (∀ f ∈ stepSub X (χ s), om X f = (χ s - cn n) • f) → IsSimple (step X (χ s))

def Reflect : Prop :=
  ∀ (n : ℕ) (X X' : GMod n) (χ : Fin n → ℂ) (s : Fin n), ScalChar X χ → ScalChar X' χ → (∀ r, χ r ≠ χ s + 1) →
    (∀ r, r ≠ s → χ r ≠ χ s) → Iso (step X (χ s)) (step X' (χ s)) → Iso X X'

def PrinSum : Prop :=
  ∀ (m : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M), GlRel E →
    ∀ x : ℂ, ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1)

def tensD (X : GMod n) : GMod n :=
  ⟨Fin n → X.V, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E,
    ((ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliTensor X.V n X.E X.gl).2.1 : _)⟩

def omD (X : GMod n) : Module.End ℂ (Fin n → X.V) := ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd X.E

def backSub (X : GMod n) (z : ℂ) : Submodule ℂ (Fin n → X.V) := (omD X).maxGenEigenspace (-z - cn n)

def back (X : GMod n) (z : ℂ) (h : ∀ a b, ∀ x ∈ backSub X z, (tensD X).E a b x ∈ backSub X z) : GMod n :=
  (tensD X).sub (backSub X z) h

def BackStable : Prop :=
  ∀ (n : ℕ) (X : GMod n) (z : ℂ), ∀ a b, ∀ x ∈ backSub X z, (tensD X).E a b x ∈ backSub X z

def DualFacts : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ), HasChar X χ →
    (∃ K : ℕ, ((List.ofFn fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))).prod) ^ K = 0) ∧
    (∀ s : Fin n, ∀ hB : (∀ a b, ∀ x ∈ backSub X (χ s), (tensD X).E a b x ∈ backSub X (χ s)),
      HasChar (back X (χ s) hB) (χ - Pi.single s 1)) ∧
    (∀ s : Fin n, Nontrivial X.V → (∀ r, χ r ≠ χ s - 1) → backSub X (χ s) ≠ ⊥)

def Unit : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hB : BackStable), ScalChar X χ → (∀ r, χ r ≠ χ s + 1) →
    (∀ r, r ≠ s → χ r ≠ χ s) → (∀ f ∈ stepSub X (χ s), om X f = (χ s - cn n) • f) →
      Iso (back (step X (χ s)) (χ s + 1) (hB n _ _)) X

def OmScal : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), ScalChar X χ → (∀ r, r ≠ s → χ r ≠ χ s) →
    ∀ f ∈ stepSub X (χ s), om X f = (χ s - cn n) • f

end CompanionTheory.RgExh.Hk
