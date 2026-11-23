import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def shift (R : RealDat3 D A3 Ks) : RealDat3 D A3 Ks := { R with lam3 := fun i t p v => R.lam3 i t p v + 1 }

theorem apply_eq_smul_of_unique_eigenvalue {M : Type} [AddCommGroup M] [Module ℂ M] (f : M → M) (h0 : f 0 = 0) (P : Submodule ℂ M) (m : ℝ)
    (h : ∀ l : ℝ, P ≠ ⊥ → (∀ x ∈ P, f x = (l : ℂ) • x) → m = l) (hA : ∃ l : ℝ, ∀ x ∈ P, f x = (l : ℂ) • x) :
    ∀ x ∈ P, f x = (m : ℂ) • x := by
  obtain ⟨l, hl⟩ := hA
  intro x hx
  by_cases hp : P = ⊥
  · rw [hp, Submodule.mem_bot] at hx
    rw [hx, h0, smul_zero]
  · rw [h l hp hl]; exact hl x hx

theorem scal_of_one {M C : Type} [AddCommGroup M] [Module ℂ M] (f : M → M) (h0 : f 0 = 0) (P : C → Submodule ℂ M) (k : C → Prop)
    (h1 : ∀ c c', k c → k c' → P c = P c') (hA : ∀ c, P c ≠ ⊥ → ∃ l : ℝ, ∀ x ∈ P c, f x = (l : ℂ) • x) :
    ∃ l : ℝ, ∀ x ∈ ⨆ (c : C) (_ : k c), P c, f x = (l : ℂ) • x := by
  by_cases hc : ∃ c, k c ∧ P c ≠ ⊥
  · obtain ⟨c, hc, hn⟩ := hc
    obtain ⟨z, hz⟩ := hA c hn
    have hle : ⨆ (c : C) (_ : k c), P c ≤ P c := iSup₂_le fun c' hc' => (h1 c' c hc' hc).le
    exact ⟨z, fun x hx => hz x (hle hx)⟩
  · refine ⟨0, fun x hx => ?_⟩
    have hle : ⨆ (c : C) (_ : k c), P c ≤ ⊥ := iSup₂_le fun c' hc' => by
      by_contra hn
      exact hc ⟨c', hc', fun e => hn e.le⟩
    rw [(Submodule.mem_bot ℂ).1 (hle hx), h0, smul_zero]

set_option maxHeartbeats 1000000 in

theorem iff_of_pin (R : RealDat3 D A3 Ks) (h : R.eigenvalue_at_base_of_scalar) :
    R.PThmA ↔ ∀ i t p, ∃ l : ℝ, ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x := by
  refine ⟨fun hA i t p => ⟨_, hA i t p⟩, fun hA i t p => ?_⟩
  exact apply_eq_smul_of_unique_eigenvalue (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) (by simp only [map_zero]) (R.Wp3 i p) _ (h i t p) (hA i t p)

def OnePart (R : RealDat3 D A3 Ks) : Prop := ∀ i p c c', R.Carries p c → R.Carries p c' → R.Wc' i c = R.Wc' i c'

def ScalC (R : RealDat3 D A3 Ks) : Prop :=
  ∀ i t c, R.Wc' i c ≠ ⊥ → ∃ l : ℝ, ∀ x ∈ R.Wc' i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x

theorem ex_of_aForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {SF} (hA : GlobalTheory.LiftRows.AForm R SF) (i t c)
    (hn : GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥) :
    ∃ l : ℝ, ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x :=
  ⟨_, (hA.choose_spec.2 i t c hn).choose_spec.2⟩

theorem scalC_of_aForm (R : RealDat3 D A3 Ks) (hA : GlobalTheory.LiftRows.AForm R.toRealDat R.SF) : ScalC R :=
  fun i t c hn => ex_of_aForm hA i t c hn

set_option maxHeartbeats 1000000 in
theorem of_scalC (R : RealDat3 D A3 Ks) (hA : ScalC R) (h : R.eigenvalue_at_base_of_scalar) (h1 : OnePart R) : R.PThmA :=
  (iff_of_pin R h).2 fun i t p =>
    scal_of_one (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) (by simp only [map_zero]) (R.Wc' i) (R.Carries p)
      (h1 i p) (hA i t)

theorem of_aForm (R : RealDat3 D A3 Ks) (hA : GlobalTheory.LiftRows.AForm R.toRealDat R.SF) (h : R.eigenvalue_at_base_of_scalar) (h1 : OnePart R) : R.PThmA :=
  of_scalC R (scalC_of_aForm R hA) h h1

end GlobalTheory.LiftScalarTest

end
