import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace LBIso IsProjOver)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.Amb

theorem exists_twist_map {k : Type} [CommRing k] {X : Scheme.{0}} {n : ℕ} (e : X ⟶ PSpace k n) [IsClosedImmersion e]
    (M : LB X) (hM : M.IsLB) :
    ∃ (t r : ℕ) (g : X ⟶ PSpace k r), g ≫ PSpace.str k r = e ≫ PSpace.str k n ∧
      cls ((O1 k r).pull g) (LB.isLB_pull (O1_isLB k r) g) =
        cls M hM + (t : ℤ) • cls ((O1 k n).pull e) (LB.isLB_pull (O1_isLB k n) e) := by
  have hO : ((O1 k n).pull e).IsLB := LB.isLB_pull (O1_isLB k n) e
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X (e ≫ PSpace.str k n) ((O1 k n).pull e) n _ hO
    (veryAmpleBy_secPull_coord e) M hM
  obtain ⟨r, u, hu⟩ := ht (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  refine ⟨t₀.toNat, r, toProj (e ≫ PSpace.str k n) u hu, toProj_str _ _ _, ?_⟩
  have hT : (tw M ((O1 k n).pull e) (t₀.toNat : ℤ)).IsLB := LB.isLB_div hM (isLB_pw hO _)
  rw [(cls_eq_iff _ hT).2 (lbIso_pullback_O1_toProj _ u hu)]
  refine (cls_div hM (isLB_pw hO _) hT).trans ?_
  rw [GlobalTheory.EffBound.cls_pw hO, neg_smul, sub_neg_eq_add]

end GlobalTheory.Amb
