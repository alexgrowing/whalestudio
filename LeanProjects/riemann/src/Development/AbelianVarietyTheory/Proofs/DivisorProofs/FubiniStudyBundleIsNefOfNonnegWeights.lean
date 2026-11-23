import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfIsFubiniStudyOfRatFnFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefOfSemiPosGeneratedBySmallSectionsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FSNef

section Sec

variable {X : Scheme.{0}} [IsIntegral X]

open Classical in

def fnOnOpen (U : X.Opens) (g : X.functionField) (hg : ∀ x ∈ U, RegAt x g) : Γ(X, U) :=
  if h : genericPoint X ∈ U then (exists_fnOf_eq h hg).choose else 0

theorem fnOf_fnOnOpen {U : X.Opens} {g : X.functionField} (hg : ∀ x ∈ U, RegAt x g) (h : genericPoint X ∈ U) :
    fnOf U h (fnOnOpen U g hg) = g := by
  classical
  rw [fnOnOpen, dif_pos h]
  exact (exists_fnOf_eq h hg).choose_spec

def secOfRat (B : LB X) (ρ : B.ι → X.functionFieldˣ) (hρ : IsRatSec B ρ) (g : X.functionField)
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) : B.Sec where
  f c := fnOnOpen (B.U c) _ (hg c)
  compat i j := fn_ext fun h => by
    change fnOf _ h (resG X inf_le_left _) =
      fnOf _ h ((B.g i j : Γ(X, B.U i ⊓ B.U j)) * resG X inf_le_right _)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_fnOnOpen, fnOf_fnOnOpen, hρ i j h]
    ring

theorem fnOf_secOfRat {B : LB X} {ρ : B.ι → X.functionFieldˣ} (hρ : IsRatSec B ρ) {g : X.functionField}
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) (c : B.ι) (h : genericPoint X ∈ B.U c) :
    fnOf _ h ((secOfRat B ρ hρ g hg).f c) = g * ρ c :=
  fnOf_fnOnOpen (hg c) h

end Sec

theorem isNef_of_isFS : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  intro hA k _ X _ p D hX M J _ f w hFS hw
  have hsemi := GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily k X p D M J f w hFS
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hFS
  let s : J → M.B.Sec := fun j => secOfRat M.B ρ hρ (f j) fun c x hx => (hreg x c hx).1 j
  have hs : ∀ j c (h : genericPoint X ∈ M.B.U c), fnOf _ h ((s j).f c) = f j * ρ c :=
    fun j c h => fnOf_secOfRat hρ _ c h
  let e := Fintype.equivFin J
  refine GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections hA k X p D hX M (Fintype.card J) (fun i => s (e.symm i)) hsemi (fun i => ?_) (fun x => ?_)
  · intro σ y
    have hy : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
    have hg : genericPoint X ∈ M.B.U (pick (M.φ σ).isLB y) := gen_mem (mem_ptsIn.1 hy)
    have hval : ∀ l, secVal p σ (s l) (pick (M.φ σ).isLB y) y =
        ratVal (f l * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y := fun l => by
      rw [secVal_apply, ← ratVal_fnOf hy hg, hs]
    rw [Weight.nsq, hval, hφ σ y _ hy]
    obtain ⟨l, hl⟩ := (hreg _ _ (mem_ptsIn.1 hy)).2
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      fun m _ => by positivity
    have hpos : 0 < ∑ m, ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      lt_of_lt_of_le (mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl)) 2) (Real.exp_pos _))
        (Finset.single_le_sum hnn (Finset.mem_univ l))
    rw [Real.exp_neg, Real.exp_log hpos, ← div_eq_mul_inv, div_le_one hpos]
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (e.symm i)))
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith [hw (e.symm i)]))
  · obtain ⟨c, hc⟩ := exists_chart M.isLB x
    obtain ⟨j, hj⟩ := (hreg x c hc).2
    refine ⟨e j, ?_⟩
    rw [e.symm_apply_apply, mem_nonzeroLocus_iff _ c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs]
    exact hj

end GlobalTheory.HSNef.FSNef
