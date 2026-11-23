import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieGeneratorsGlRelations

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

def SmF (n : ℕ) : Submodule ℂ (Mat n → ℂ) where
  carrier := {h | ContDiffOn ℝ ∞ h (GLs n) ∧ ∀ g, g ∉ GLs n → h g = 0}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c a ha := ⟨contDiffOn_const.smul ha.1, fun g hg => by simp [ha.2 g hg]⟩

theorem indicator_Rd_mem (X : Mat n) (h : SmF n) : (GLs n).indicator (Rd X h.1) ∈ SmF n := by
  refine ⟨(GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X h.2.1).congr fun g hg => Set.indicator_of_mem hg _,
    fun g hg => Set.indicator_of_notMem hg _⟩

def DR (X : Mat n) : Module.End ℂ (SmF n) where
  toFun h := ⟨(GLs n).indicator (Rd X h.1), indicator_Rd_mem X h⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      have db := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth b.2.1 hg
      simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_of_mem hg, Rd]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_add_apply' da db _
    · simp [Set.indicator_of_notMem hg]
  map_smul' c a := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_of_mem hg, Rd, RingHom.id_apply, smul_eq_mul]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply da c _
    · simp [Set.indicator_of_notMem hg]

def Kf (a b : Fin n) : Module.End ℂ (SmF n) := e1 DR a b + e2 DR a b

def ev1 : SmF n →ₗ[ℂ] ℂ where
  toFun h := h.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Pb (lev : Fin n → ℕ) : Set (Mat n) := {p | p ∈ GLs n ∧ ∀ a b, lev a < lev b → p a b = 0}

def Eqv (lev : Fin n → ℕ) (φ : Mat n → ℂ) : Submodule ℂ (SmF n) where
  carrier := {h | ∀ p ∈ Pb lev, ∀ g ∈ GLs n, h.1 (p * g) = φ p * h.1 g}
  add_mem' {a b} ha hb p hp g hg := by
    simp only [Submodule.coe_add, Pi.add_apply, ha p hp g hg, hb p hp g hg, mul_add]
  zero_mem' p _ g _ := by simp
  smul_mem' c a ha p hp g hg := by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha p hp g hg, smul_eq_mul]
    ring

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ)

def yZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a => lam a - muZ lam lev a

def dif (v : Fin n → ℤ) (j : Fin n) : ℤ := v j - if h : (j : ℕ) + 1 < n then v ⟨j + 1, h⟩ else 0

def ini (j : Fin n) : Fin (j + 1) → Fin n := Fin.castLE j.isLt

def lm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) (ini j)).det

def gm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ).det

def fRaw (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Mat n → ℂ :=
  (GLs n).indicator fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j

def cyc (f : SmF n) : Submodule ℂ (SmF n) :=
  (Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}).toSubmodule.map
    (LinearMap.applyₗ f)

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit k).ne_zero

theorem DR_apply (X : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (DR X h).1 g = Rd X h.1 g :=
  Set.indicator_of_mem hg _

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (e1 DR a b h).1 g = Eu true a b h.1 g := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, DR_apply _ _ hg, Eu, Pi.add_apply, if_true, smul_eq_mul]
  ring

theorem liftOneFormsToCompatible_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (f1 DR a b h).1 g = Eu false a b h.1 g := by
  simp [f1, DR_apply _ _ hg, Eu]
  ring

section K

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]

def ipK (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) (x y : SmF n) : ℂ := ∫ k, conj (x.1 k.1) * y.1 k.1 ∂κ

end K

end GlobalTheory.CompanionTheory.ModelS
