import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFrame
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftRingMembership
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftValuationPoints
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFiltration
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in
theorem u1link_pf : FirstFrameOfModels := by
  intro D HW F Cm hA hdR hDi hML hMF
  intro l _ hl K LL hG π' E hp9 T₁ T₂ Fm S η m h' up b c α β hIF hHyp
  have hc2 := hHyp.2.1
  have hj2 := hHyp.2.2.2.2.1
  have hηb := hHyp.2.2.2.2.2.1
  have hbS := hHyp.2.2.2.2.2.2.1
  have hh' := hHyp.2.2.2.2.2.2.2.1
  have hm := hHyp.2.2.2.2.2.2.2.2.1
  have hjI : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hd := hj2 τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hp9 h' hh' c α β hIF T₂ hc2 hjI
  have hML2 := hML l hl K LL hG π' E hp9 h' hh' T₂ hc2 hjI c
  have hR := UniversalLiftFrames.universal_lift_ring_membership D HW F Cm hA hl K LL hG π' E hp9
  have hT := UniversalLiftFrames.embeddings_card_le_degree D HW K LL hG c
  have hτs := hT.choose_spec.1
  have hcard := hT.choose_spec.2
  have hB := UniversalLiftFrames.universal_lift_basis D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c
  have hrep := hB.choose_spec.choose_spec.choose_spec.choose
  have hbrep := hB.choose_spec.choose_spec.choose_spec.choose_spec
  refine UniversalLiftFrames.universal_lift_frame (W := (HW l).W K 1 LL hG) (PD := (D.loc l).PD K) (GenPf.isDVR (D.loc l) LL)
    (GenPf.isFractionRing LL) Fm (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π'
    (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c S η m up b α β hIF hc2 hjI hMF2 hML2 hM
    hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1 hR.2.2.2.2.2.2 hT.choose hτs hcard ?_ ?_ hbS ?_ ?_ ?_ hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep ?_ ?_ ?_ ?_ ?_ ?_ ?_ hHyp
  · exact fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt
  · exact fun τ => Nat.lt_of_le_of_lt (Nat.zero_le _) (hηb τ)
  · exact fun τ ζ hpt => ⟨(UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).1,
      (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.1⟩
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.2
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).2
  · exact fun τ ζ ζ' hpt hpt' k => UniversalLiftFrames.universal_lift_valuation_points D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ ζ' hpt hpt'
      (hB.choose_spec.choose_spec.choose k) (hrep k)
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).2
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).2

end Formalism.MainNotions.N.Ln34
