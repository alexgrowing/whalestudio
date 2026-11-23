import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FrameMoves

variable {D : D7}

theorem mulVec_of_grpOff (S : HSp D) {v : Pl D} {h : GA D S} (hh : h ∈ grpOff S (· = v))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : mt S h *ᵥ y = y := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hy' : ∀ j, GlobalTheory.FinPlLoc.idem D (· = v) * y j = y j := fun j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy j)
  ext i
  calc (mt S h *ᵥ y) i = ∑ j, mt S h i j * y j := rfl
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← hy' j]
        ring
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
        simp_rw [hij]
    _ = y i := by
        simp [Matrix.one_apply, hy' i]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_pr_of_grpOff (p : SplitPt D k) (S : HSp D) {h : GA D S} (hh : h ∈ grpOff S (· = p.v)) :
    (mt S h).map p.pr = 1 := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = p.v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = p.v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = p.v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hpr : ∀ x, p.pr x = p.pr (p.e * x) := fun x => by rw [← p.sec_pr, p.pr_sec]
  have he : GlobalTheory.FinPlLoc.idem D (· = p.v) * p.e = p.e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt p)
  rw [← Matrix.map_one p.pr (map_zero _) (map_one _)]
  ext i j
  simp only [Matrix.map_apply]
  rw [hpr, hpr ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j), ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _) p.e,
    mul_assoc, hij i j, ← mul_assoc]

theorem moves_iff_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  intro D k _ _ _ _ p A n _ _ β L Λ hL hΛ κ
  obtain ⟨h1, -, -, h4, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p A n β
  obtain ⟨Λ', -, hΛ', hK⟩ := h4 L hL
  have hΛeq : Λ' = Λ := by
    ext x
    rw [hΛ' x, hΛ x]
  subst hΛeq
  obtain ⟨hv, hvAt, h', h'Off, rfl⟩ := (GlobalTheory.FinPlLoc.part_grp (· = p.v) A).1 κ
  obtain ⟨g, rfl⟩ := (h1 hv).1 hvAt
  have hoff : coordHom A p.pr β.b β.b' β.bb' β.b'b h' = 1 := by
    refine Units.ext ?_
    rw [coordHom_val, map_pr_of_grpOff p A h'Off, Matrix.mul_one, β.b'b]
    rfl
  have hg : coordHom A p.pr β.b β.b' β.bb' β.b'b (β.gl g) = g :=
    ((eq_coordHom_iff A p.pr β.b β.b' β.bb' β.b'b (β.gl g) g).1 (β.gl_mat g)).symm
  rw [map_mul, hoff, mul_one, hg, ← hK g]
  constructor
  · intro hm
    refine ⟨hvAt, fun y hy => ?_⟩
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]
  · rintro ⟨-, hm⟩ y hy
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]

end GlobalTheory.FrameMoves

end
