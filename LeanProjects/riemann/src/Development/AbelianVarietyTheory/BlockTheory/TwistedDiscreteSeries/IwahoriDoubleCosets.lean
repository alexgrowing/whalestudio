import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

section General

variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]

def IsIntegralOp (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ (v : V) (l : Module.Dual ℂ V),
    Integrable (fun g => f g * l (π g v)) μ ∧ l (A v) = ∫ g, f g * l (π g v) ∂μ

theorem IsIntegralOp.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {A B : V →ₗ[ℂ] V}
    (hA : IsIntegralOp μ π f A) (hB : IsIntegralOp μ π f B) : A = B := by
  ext v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, (hA v l).2, (hB v l).2, sub_self]

def HasFinTrace (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (LinearMap.range A) ∧
    LinearMap.trace ℂ (LinearMap.range A)
      (A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        fun v _ => LinearMap.mem_range_self A v) = c

def HasTrace (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (c : ℂ) : Prop :=
  ∃ A : V →ₗ[ℂ] V, IsIntegralOp μ π f A ∧ HasFinTrace A c

theorem HasTrace.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {c d : ℂ}
    (hc : HasTrace μ π f c) (hd : HasTrace μ π f d) : c = d := by
  obtain ⟨A, hA, -, rfl⟩ := hc
  obtain ⟨B, hB, -, rfl⟩ := hd
  obtain rfl := hA.unique hB
  rfl

end General

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

def unipO : Subgroup (GL n k) := unipB k n ⊓ KO k n

def unipLowerOne : Subgroup (GL n k) := unipBLower k n ⊓ KOne k n

variable {k n}

def Contracts (t : n → kˣ) : Prop :=
  (∀ u ∈ unipO k n, diagT k n t * u * (diagT k n t)⁻¹ ∈ unipO k n) ∧
    ∀ u ∈ unipLowerOne k n, (diagT k n t)⁻¹ * u * diagT k n t ∈ unipLowerOne k n

example : Contracts (1 : n → kˣ) := ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩

def deltaB (t : n → kˣ) : ℝ := ∏ i, ∏ j with i < j, nabs k (t i / t j)

theorem deltaB_pos (t : n → kˣ) : 0 < deltaB t :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => nabs_pos' k _

theorem deltaB_eq_modulus (t : n → kˣ) :
    deltaB t = modulus k (fun _ : n => Unit) (leviTorus k n t) := (modulus_torus t).symm

def iwahoriCoset (t : n → kˣ) : Set (GL n k) :=
  {g | ∃ a ∈ iwahori k n, ∃ b ∈ iwahori k n, g = a * diagT k n t * b}

def cosetInd (t : n → kˣ) : GL n k → ℂ := (iwahoriCoset t).indicator fun _ => 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped Classical in

def IsExponents (π : Representation ℂ (GL n k) V) (E : Multiset ((n → kˣ) →* ℂˣ)) : Prop :=
  (∀ χ ∈ E, ∀ s ∈ torusO k n, χ s = 1) ∧ ∀ χ, (E.count χ : ℕ∞) = expMult π χ

theorem IsExponents.unique {π : Representation ℂ (GL n k) V} {E E' : Multiset ((n → kˣ) →* ℂˣ)}
    (h : IsExponents π E) (h' : IsExponents π E') : E = E' := by
  classical
  ext χ
  have := (h.2 χ).trans (h'.2 χ).symm
  have h2 := Nat.cast_injective this
  convert h2

variable (k n)

def DominantContracts : Prop :=
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ a : n → ℤ, Antitone a → Contracts fun i => ϖ ^ a i

def TraceFormula : Prop :=
  ∀ [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π →
    FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) ∧
    (∀ t : n → kˣ, Contracts t →
      HasTrace μ π (cosetInd t)
        ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
          LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t))) ∧
    ∃ E : Multiset ((n → kˣ) →* ℂˣ), IsExponents π E ∧
      ∀ t : n → kˣ, Contracts t →
        HasTrace μ π (cosetInd t)
          ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
            (E.map fun χ => (χ t : ℂ)).sum)

end Local

def IwahoriTrace : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ),
    DominantContracts k (Fin r) ∧ TraceFormula k (Fin r)

def IwahoriTraceOfBorelCasselman : Prop := GlobalTheory.Published.BorelCasselman → IwahoriTrace

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
