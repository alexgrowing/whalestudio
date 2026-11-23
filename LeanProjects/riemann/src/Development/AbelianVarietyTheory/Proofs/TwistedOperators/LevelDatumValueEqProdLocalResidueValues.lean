import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

theorem level_character_congr {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ}
    {P Q : Formalism.L2.DIV.LevelP Pg r ℂ} (h : P = Q) (x : Formalism.L2.DIV.G0 Pg r) (hx : x ∈ P.H) (hx' : x ∈ Q.H) :
    P.chi ⟨x, hx⟩ = Q.chi ⟨x, hx'⟩ := by
  subst h; rfl

theorem omegaG_eq_prod_gLoc : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  intro D a b L χ Hl cl hP y
  classical
  have hmem : ∀ x, x ∈ L.P.H ↔ ∀ PP, x PP ∈ Hl PP := by
    intro x; rw [hP]; simp [Formalism.L2.DIV.LevelP.ofLocal, Subgroup.mem_pi]
  by_cases hall : ∀ PP : ↥L.Pg, LowZero a (y PP.1) ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP.1),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1) ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ Hl PP
  · have hG : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H :=
      ⟨fun PP hPP => (hall ⟨PP, hPP⟩).1, fun PP => (hall PP).2.choose, fun PP => (hall PP).2.choose_spec.1,
        fun PP => (hall PP).2.choose_spec.2.1, (hmem _).2 fun PP => (hall PP).2.choose_spec.2.2⟩
    have key : ∀ PP, hG.2.choose PP = (hall PP).2.choose := fun PP =>
      Units.ext ((hG.2.choose_spec.1 PP).trans ((hall PP).2.choose_spec.1).symm)
    rw [omegaG, dif_pos hG]
    have hloc : ∀ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) =
        ((cl PP ⟨Formalism.L2.DIV.upperLeftBlock L.hr (hall PP).2.choose, (hall PP).2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
          (∏ i ∈ Finset.range L.s,
            ((L.cg (i + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) (hall PP).2.choose) : ℂˣ) : ℂ)) *
          (((χ PP.1 (Matrix.GeneralLinearGroup.det (hall PP).2.choose)) : ℂˣ) : ℂ)⁻¹ := fun PP => by
      rw [gLoc, dif_pos (hall PP)]
    rw [Finset.prod_congr rfl fun PP _ => hloc PP]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hx' : (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (hG.2.choose PP)) ∈ (Formalism.L2.DIV.LevelP.ofLocal Hl cl).H := by
      rw [← hP]; exact hG.2.choose_spec.2.2
    congr 1
    congr 1
    · rw [level_character_congr hP _ _ hx', ← Units.coe_prod]
      refine congrArg Units.val ((MonoidHom.finsetProd_apply _ _ _).trans (Finset.prod_congr rfl fun PP _ => ?_))
      refine congrArg (cl PP) (Subtype.ext ?_)
      exact congrArg (Formalism.L2.DIV.upperLeftBlock L.hr) (key PP)
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
  · have hG : ¬ ((∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H) := by
      rintro ⟨h1, g, hg1, hg2, hg3⟩
      exact hall fun PP => ⟨h1 PP.1 PP.2, g PP, hg1 PP, hg2 PP, (hmem _).1 hg3 PP⟩
    push_neg at hall
    obtain ⟨PP, hPP⟩ := hall
    rw [omegaG, dif_neg hG]
    refine (Finset.prod_eq_zero (Finset.mem_univ PP) ?_).symm
    rw [gLoc, dif_neg]
    rintro ⟨h1, g, hg1, hg2, hg3⟩
    exact hPP h1 g hg1 hg2 hg3

end GlobalTheory.StepVec

end
