import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eventuallyEq_of_agree_GLs {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) {x : Mat n}
    (hx : x ∈ GLs n) : F =ᶠ[nhds x] F' := by
  have ho : IsOpen (GLs n) := by
    have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne.preimage this
  exact Filter.eventuallyEq_of_mem (ho.mem_nhds hx) h

theorem Rd_agree_GLs (X : Mat n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Rd X F x = Rd X F' x := by
  intro x hx
  simp only [Rd, (eventuallyEq_of_agree_GLs h hx).fderiv_eq]

theorem Eu_agree_GLs (s : Bool) (a b : Fin n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Eu s a b F x = Eu s a b F' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_agree_GLs _ h x hx]

theorem Epow_agree_GLs (s : Bool) (m : ℕ) (a b : Fin n) {F F' : Mat n → V}
    (h : ∀ g ∈ GLs n, F g = F' g) : ∀ x ∈ GLs n, Epow s m a b F x = Epow s m a b F' x := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    by_cases hab : a = b
    · simpa [Epow, hab] using h x hx
    · simp [Epow, hab]
  | succ m ih =>
    intro x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_agree_GLs s a c (ih c b) x hx

theorem gel_agree_GLs (s : Bool) (m : ℕ) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, gel s m F x = gel s m F' x := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => Epow_agree_GLs s m a a h x hx

end Local

theorem zOp_agree_GLs : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) (F F' : Mat n → V), (∀ g ∈ GLs n, F g = F' g) →
    ∀ x ∈ GLs n, zOp w F x = zOp w F' x := by
  intro n V _ _ w
  induction w with
  | nil => exact fun F F' h x hx => h x hx
  | cons p w ih => exact fun F F' h => gel_agree_GLs p.1 p.2 (ih F F' h)

end GlobalTheory.CompanionTheory.WaveMult
