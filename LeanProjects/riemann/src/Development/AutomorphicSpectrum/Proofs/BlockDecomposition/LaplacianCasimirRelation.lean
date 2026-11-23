import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y - v y) g = Rd X u g - Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv (g * X)

theorem Rd_add_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y + v y) g = Rd X u g + Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv (g * X)

theorem Rd_sq_sub (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X - X') (Rd (X - X') f) g =
      Rd X (Rd X f) g - Rd X (Rd X' f) g - (Rd X' (Rd X f) g - Rd X' (Rd X' f) g) := by
  have e : Rd (X - X') f = fun y => Rd X f y - Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_sub X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_sub, Rd_sub_fun X h1 h2 hg, Rd_sub_fun X' h1 h2 hg]

theorem Rd_sq_add (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X + X') (Rd (X + X') f) g =
      Rd X (Rd X f) g + Rd X (Rd X' f) g + (Rd X' (Rd X f) g + Rd X' (Rd X' f) g) := by
  have e : Rd (X + X') f = fun y => Rd X f y + Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_add X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_add, Rd_add_fun X h1 h2 hg, Rd_add_fun X' h1 h2 hg]

abbrev skY (a c : Fin n) : Mat n := Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ)

abbrev skZ (a c : Fin n) : Mat n := Matrix.single a c Complex.I + Matrix.single c a Complex.I

theorem Lap_eq (hO : OmFormula) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Lap f g = -Om f g + (-(1 / 2 : ℂ)) • ∑ a, ∑ c,
      (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) := by
  set P : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single a c (1 : ℂ)) f) g with hP
  set Q : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single a c Complex.I) f) g with hQ
  set M : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single c a (1 : ℂ)) f) g with hM
  set N : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g with hN
  have hY : ∀ a c, Rd (skY a c) (Rd (skY a c) f) g = P a c - M a c - (M c a - P c a) := fun a c =>
    Rd_sq_sub _ _ hf hg
  have hZ : ∀ a c, Rd (skZ a c) (Rd (skZ a c) f) g = Q a c + N a c + (N c a + Q c a) := fun a c =>
    Rd_sq_add _ _ hf hg
  have hS : ∑ p, Rd (bs p) (Rd (bs p) f) g = ∑ a, ∑ c, P a c + ∑ a, ∑ c, Q a c := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, GlobalTheory.CompanionTheory.SecBd.basis_true_eq_single, GlobalTheory.CompanionTheory.SecBd.bs_f,
      Finset.sum_add_distrib, hP, hQ]
  have hOm : Om f g = ∑ a, ∑ c, M a c - ∑ a, ∑ c, N a c := by
    rw [hO n V f hf g hg]
    simp only [Finset.sum_sub_distrib, hM, hN]
  have swap : ∀ F : Fin n → Fin n → V, ∑ a, ∑ c, F c a = ∑ a, ∑ c, F a c := fun F => Finset.sum_comm
  have hT : ∑ a, ∑ c, (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) =
      (2 : ℂ) • (∑ a, ∑ c, P a c) - (2 : ℂ) • (∑ a, ∑ c, M a c) +
        ((2 : ℂ) • (∑ a, ∑ c, Q a c) + (2 : ℂ) • (∑ a, ∑ c, N a c)) := by
    simp only [hY, hZ, Finset.sum_add_distrib, Finset.sum_sub_distrib, swap M, swap P, swap N, swap Q]
    module
  show -∑ p, Rd (bs p) (Rd (bs p) f) g = _
  rw [hS, hOm, hT]
  module

theorem lap_sec : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  intro n E _ hO
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewZ a c)
  have sq : ∀ (Y : Mat n) (B : E.V →L[ℂ] E.V), (∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) →
      ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y (Rd Y f) g = (B * B) (f g) := by
    intro Y B h f hf g hg
    have e : Set.EqOn (Rd Y f) (fun y => B (f y)) (GLs n) := fun y hy => h f hf y hy
    rw [GlobalTheory.CompanionTheory.RCalc.Rd_congr Y e hg, GlobalTheory.CompanionTheory.SobOpsPf.Rd_post Y B hf.1 hg, h f hf g hg]
    rfl
  refine ⟨(-(1 / 2 : ℂ)) • ∑ a, ∑ c, (BY a c * BY a c + BZ a c * BZ a c), fun f hf g hg => ?_⟩
  rw [Lap_eq hO hf.1 hg]
  congr 1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [sq _ _ (hBY a c) f hf g hg, sq _ _ (hBZ a c) f hf g hg]

end GlobalTheory.CompanionTheory.FcSmooth
