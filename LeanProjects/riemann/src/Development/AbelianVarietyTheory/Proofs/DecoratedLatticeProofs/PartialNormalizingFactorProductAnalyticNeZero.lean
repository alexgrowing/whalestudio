import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

noncomputable section

namespace GlobalTheory.LFun

open NumberField IsDedekindDomain

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_lt_re_dv_arg {a i : ℕ} (hi : i ∈ Finset.range a) {s : ℂ} (hs : 0 < s.re) :
    1 < (2 * s + a - i : ℂ).re := by
  have : (i : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hi
  simp
  linarith

theorem dv_ne_zero_of_re_pos (a b : ℕ) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    dv E a b v s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero ((converges_etaFam (E := E) ∅ (b + i) (one_lt_re_dv_arg hi hs)).1 v (Set.notMem_empty v))

theorem dSfun_ne_zero_of_re_pos (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    dSfun E S a b s ≠ 0 := by
  rw [dSfun_eq S a b hs]
  exact Finset.prod_ne_zero_iff.2 fun i hi => (converges_etaFam S (b + i) (one_lt_re_dv_arg hi hs)).ne_zero

theorem differentiableOn_dSfun (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) :
    DifferentiableOn ℂ (dSfun E S a b) {s | 0 < s.re} := by
  have h : DifferentiableOn ℂ (fun s : ℂ => ∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i))
      {s | 0 < s.re} := by
    refine DifferentiableOn.fun_finsetProd fun i hi => ?_
    refine (bounded_etaFam (E := E) S (b + i)).differentiableOn.comp
      (f := fun s : ℂ => 2 * s + a - i) (by fun_prop) fun s hs => ?_
    simpa only [zero_add, Set.mem_ofPred_eq] using one_lt_re_dv_arg hi hs
  exact h.congr fun s hs => dSfun_eq S a b hs

end Ext

end GlobalTheory.LFun

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem dSfun_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := fun _ S a b =>
  ⟨(GlobalTheory.LFun.differentiableOn_dSfun S a b).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    fun _ hs => ⟨GlobalTheory.LFun.dSfun_ne_zero_of_re_pos S a b hs, fun v => GlobalTheory.LFun.dv_ne_zero_of_re_pos a b v hs,
      (GlobalTheory.LFun.hasProd_dv S a b hs).multipliable.hasProd⟩⟩

end GlobalTheory.Core.Rk.IP

end
