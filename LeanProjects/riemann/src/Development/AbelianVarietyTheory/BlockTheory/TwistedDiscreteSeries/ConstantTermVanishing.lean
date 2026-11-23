import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)

def stdParabolic (k : Type) [Field k] (r a : ℕ) : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j : Fin r, j.val < a → a ≤ i.val → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := fun i j hj hi => Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' := fun {g h} hg hh i j hj hi => by
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < a
    · rw [hg i l hl hi, zero_mul]
    · rw [hh l j hj (not_lt.1 hl), mul_zero]
  inv_mem' := fun {g} hg i j hj hi => by
    have hb : (g : Matrix (Fin r) (Fin r) k).BlockTriangular fun l => if l.val < a then (0 : ℕ) else 1 := by
      intro i j h
      by_cases h1 : j.val < a <;> by_cases h2 : i.val < a <;> simp [h1, h2] at h
      exact hg i j h1 (not_lt.1 h2)
    letI := g.invertible
    have := Matrix.blockTriangular_inv_of_blockTriangular hb
    rw [Matrix.coe_units_inv]
    exact this (by simp [hj, not_lt.2 hi])

def InConjParabolic {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k)) (a : ℕ) : Prop :=
  ∃ g : GL (Fin r) k, ∀ p ∈ H, g⁻¹ * p * g ∈ stdParabolic k r a

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parAt {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) : Subgroup (GL (Fin V.rank) (Fv D.host.F v)) :=
  (PLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))

def ParabolicAtSplitPlaces : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (T : TypeDataG V) (𝔉 : IsoFlag V), 𝔉.Proper →
    ∃ a : ℕ, 0 < a ∧ 2 * a + 1 ≤ V.rank ∧ ∀ v : T.S,
      InConjParabolic (parAt 𝔉 (T.frame v)) a ∧ InConjParabolic (parAt 𝔉 (T.frame v)) (V.rank - a)

def UnipIntegralsVanish {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (f : GA D V → ℂ) : Prop :=
  ∀ (ν : Measure (NA 𝔉)) [ν.IsHaarMeasure] (x y : GA D V),
    Integrable (fun n : NA 𝔉 => f (x * n * y)) ν ∧ ∫ n : NA 𝔉, f (x * n * y) ∂ν = 0

def TestFnConstTermVanish : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V), HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (U : AuxiliaryPlaceHermitianSpace V)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (f : GA D V → ℂ), IsTestFnG M T U μa μf f →
    ∀ 𝔉 : IsoFlag V, 𝔉.Proper → UnipIntegralsVanish 𝔉 f ∧ UnipIntegralsVanish 𝔉 (starFn f)

def ParabolicAndConstTerm : Prop := ParabolicAtSplitPlaces ∧ TestFnConstTermVanish

example (k : Type) [Field k] (g : GL (Fin 2) k) :
    g ∈ stdParabolic k 2 1 ↔ (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  change (∀ i j : Fin 2, _) ↔ _
  simp [Fin.forall_fin_two]

example (k : Type) [Field k] (r a : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical k r a ⊆ stdParabolic k r a := fun u hu i j hj hi => by
  by_contra h
  have := hu i j (by rwa [Matrix.one_apply_ne (by rintro rfl; omega)])
  omega

example {D : D7} {V : HSp D} (𝔉 : IsoFlag V) : ∃ ν : Measure (NA 𝔉), ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩

example {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {φ : GA D V → ℝ} (hc : Continuous φ) (h0 : 0 ≤ φ)
    (h : UnipIntegralsVanish 𝔉 fun g => (φ g : ℂ)) : φ = 0 := funext fun x => by
  obtain ⟨h1, h2⟩ := h Measure.haar x 1
  have hc' : Continuous fun n : NA 𝔉 => φ (x * n * 1) := hc.comp (by fun_prop)
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero,
    integral_eq_zero_iff_of_nonneg (f := fun n : NA 𝔉 => φ (x * n * 1)) (fun n => h0 _) (by simpa using h1.re)] at h2
  simpa using congrFun ((hc'.ae_eq_iff_eq _ continuous_zero).1 h2) 1

end GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

end
