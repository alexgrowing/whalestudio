import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem derFam_expand_words : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  intro n ε F hF d b c hb hlin m
  induction m with
  | zero =>
    intro Y _ g _
    simp
  | succ m ih =>
    intro Y hY g hg
    have hwb : ∀ J : Fin m → Fin d, ∀ Z ∈ List.ofFn (fun j => b (J j)), Z ∈ lieSet ε := by
      intro J Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hb _
    have hwY : ∀ Z ∈ List.ofFn (fun j : Fin m => Y j.succ), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hY _
    have key : ∀ i, F (b i :: List.ofFn (fun j : Fin m => Y j.succ)) g =
        ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g := by
      intro i
      have h1 := hF (List.ofFn fun j : Fin m => Y j.succ) hwY (b i) (hb i) g hg
      have h2 : HasDerivAt (fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
          F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)))
          (∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g) 0 := by
        apply HasDerivAt.fun_sum
        intro J _
        exact (hF _ (hwb J) (b i) (hb i) g hg).const_mul _
      have heq : (fun t : ℝ => F (List.ofFn fun j : Fin m => Y j.succ) (g * NormedSpace.exp (t • b i))) =
          fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
            F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)) := by
        funext t
        exact ih (fun j => Y j.succ) (fun j => hY _) _ (mul_mem_UJ hg (exp_mem_UJ (hb i) t))
      rw [heq] at h1
      exact h1.unique h2
    rw [List.ofFn_succ, hlin _ hwY (Y 0) (hY 0) g hg]
    simp_rw [key, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

end GlobalTheory.TypeSum
