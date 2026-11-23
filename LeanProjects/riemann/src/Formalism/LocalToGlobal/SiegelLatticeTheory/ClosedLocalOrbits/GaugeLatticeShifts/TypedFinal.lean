import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trExistsC_of (hP : ∀ (D : D7) (X : HidaSetting D), SatGram.PsiCond X) : TRExistsC :=
  fun D X _ => SatGram.typedRed_exists' SatGramLoc.split_prime_local_holds SatGramLoc.reduction_structure_holds (hP D X)

theorem psiCond_holds {D : D7} (X : HidaSetting D) : SatGram.PsiCond X :=
  open Formalism.L2.SG.Pf.SatGram in
  psi_conductor_all_places D X

theorem trExistsC_holds : TRExistsC :=
  trExistsC_of (fun _ X => psiCond_holds X)

section

variable {D : D7} (X : HidaSetting D)

theorem typed_count_holds (TR : TypedRed X) (i : Fin 2) :
    Fintype.card {v : TR.Pl // Fintype.card (TR.Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  typed_count (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR i

theorem tt_eq_holds (TR : TypedRed X) :
    ∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) =
      (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F * (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
  have h0 := typed_count_holds X TR 0
  have h1 := typed_count_holds X TR 1
  rw [Fintype.card_subtype] at h0 h1
  have hfilt : Finset.univ.filter (fun v => ¬ Fintype.card (TR.Fq v) = D.host.g 0) =
      Finset.univ.filter (fun v => Fintype.card (TR.Fq v) = D.host.g 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (TR.card_q v).resolve_left h
    · intro h h'
      exact D.host.g_ne (h'.symm.trans h)
  have e0 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (TR.Fq v) = D.host.g 0),
      (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) = (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
    rw [Finset.prod_congr rfl (g := fun _ => (1 + 3 / (D.host.g 0 : ℝ)))
      (fun v hv => by rw [(Finset.mem_filter.mp hv).2]), Finset.prod_const, h0]
  have e1 : ∏ v ∈ Finset.univ.filter (fun v => ¬ Fintype.card (TR.Fq v) = D.host.g 0),
      (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) = (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
    rw [hfilt, Finset.prod_congr rfl (g := fun _ => (1 + 3 / (D.host.g 1 : ℝ)))
      (fun v hv => by rw [(Finset.mem_filter.mp hv).2]), Finset.prod_const, h1]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun v => Fintype.card (TR.Fq v) = D.host.g 0), e0, e1]

theorem gamma_one_typed_places_holds (TR : TypedRed X) :
    Gam1 TR = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      (Formalism.L2.SG.TypedSets.glkC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) /
        (Formalism.L2.SG.TypedSets.ukC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  gamma_one_eq_prod_typed_places (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR

theorem gSplitX_holds : Formalism.L2.SG.LocVol.GSplitX X := by
  intro p
  have hg0 : D.host.g 0 ≠ 0 := (D.host.g_prime 0).ne_zero
  have hg1 : D.host.g 1 ≠ 0 := (D.host.g_prime 1).ne_zero
  have hty := (Formalism.L2.SG.TypedSets.mem_typSet X.B.I.F _ _ hg0 hg1 p.1).1 p.2
  have hg : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [X.g_eq, Nat.cast_mul]
    rcases hty with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  refine ⟨?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Formalism.L2.SG.LocVol.gAt
    split_ifs with h0
    · exact gResCard_holds X p.1 0 h0
    · exact gResCard_holds X p.1 1 (hty.resolve_left h0)
  · unfold Formalism.L2.SG.LocVol.etaV
    rw [if_pos (split_at_g X p.1 hg)]

end

end Formalism.L2.SG.Pf
