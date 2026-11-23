import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

open scoped NNReal
open Set Metric Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont

def Dominated {G : Type} [Group G] (K : Subgroup G) (φ ψ : G → ℂ) : Prop :=
  ∀ c : K →₀ ℂ, (∀ g, (c.sum fun k z => z * φ (g * k)) = 0) → ∀ g, (c.sum fun k z => z * ψ (g * k)) = 0

def domSet {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ) (φ : G → ℂ) :
    Set (G → ℂ) := {ψ | IndLaw δ χ t ψ ∧ Dominated K φ ψ}

variable {D : D7}

def RegAt (T : HSp D) (e : ℂ → GA D T → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D T → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * cont (fun z => e z g) s) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D T => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height T g ^ N

def ContMod (T : HSp D) (e : ℂ → GA D T → ℂ) : Prop := (∀ g, Continues fun z => e z g) ∧ ∀ s₀, ∃ k, RegAt T e s₀ k

def detChar {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (μ : (AE D)ˣ →* Circle) : stab d →* Circle :=
  μ.comp (Matrix.GeneralLinearGroup.det.comp (onX d))

abbrev lev (T : HSp D) (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)) : Subgroup (GA D T) := AdelicU.levelAll D.sp.cm.sig T.gram L a

structure IsLevel (T : HSp D) (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)) : Prop where
  lat : Submodule.IsLattice D.host.E L
  dual : ∀ v, AdelicU.IsSelfDualAt D.sp.cm.sig T.gram L v
  maj : AdelicU.IsMajorantFrame D.sp.cm.sig T.gram a

theorem Dominated.refl {G : Type} [Group G] (K : Subgroup G) (φ : G → ℂ) : Dominated K φ φ := fun _ h => h

theorem exists_isLevel (T : HSp D) : ∃ a, IsLevel T (AdelicU.frameLat T) a :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj T
  ⟨a, AdelicU.SelfDual.isLattice_frameLat T, AdelicU.SelfDual.isSelfDualAt_frameLat D T, ha⟩

theorem lev_frameLat (T : HSp D) (a : GL (Fin T.rank) (AE D)) : lev T (AdelicU.frameLat T) a = Kmax T a := rfl

theorem Dominated.const_mul {G : Type} [Group G] (K : Subgroup G) (φ : G → ℂ) (a : ℂ) :
    Dominated K φ fun g => a * φ g := fun c h g => by
  have := congrArg (a * ·) (h g)
  simp only [Finsupp.sum, Finset.mul_sum, mul_zero] at this ⊢
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Dominated.eq_zero {G : Type} [Group G] {K : Subgroup G} {ψ : G → ℂ} (h : Dominated K (fun _ => 0) ψ) (g : G) :
    ψ g = 0 := by
  have := h (Finsupp.single 1 1) (fun _ => by simp) g
  simpa using this

end GlobalTheory.EisCont

end
