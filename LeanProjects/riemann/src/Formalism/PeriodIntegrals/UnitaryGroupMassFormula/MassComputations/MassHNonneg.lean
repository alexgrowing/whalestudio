import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StabFiniteOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassUnfoldHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.CountableRatOf

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem massH_nonneg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 ≤ massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) :=
  finsum_nonneg fun _ => inv_nonneg.2 (Nat.cast_nonneg _)

theorem massAll_of (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) : MassAll := by
  intro D X hb u hT
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hN := X.measW_norm u
  have hcs := hH X u
  have hfin : MassFinite (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) (GamH X u) (KH X u) :=
    ⟨hC X u, stabFinite_of hH hK X u⟩
  obtain ⟨𝓕, h𝓕⟩ := fdExistsH_holds X u
  have hU := massUnfold_holds X u hN hcs (hK X).1 (hK X).2 hfin 𝓕 h𝓕
  have hcov : covol (X.measW u).μH = ((X.measW u).μH 𝓕).toReal :=
    covol_eq_of_fd X.B.I.cm.sig X.B.I.J _ (X.measW u).μH hN.1.toIsMulLeftInvariant 𝓕 h𝓕
  have hV := volHTie_holds X hb u hT

  have h1 := hN.2.1
  have h2 := hN.2.2.1
  have ha0 : (X.measW u).μHinf Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have haT : (X.measW u).μHinf Set.univ ≠ ⊤ :=
    (h1.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ (hH X u))).ne
  have hKo : IsOpen (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hK X).2.preimage continuous_subtype_val
  have hb0 : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ 0 :=
    h2.toIsOpenPosMeasure.open_pos _ hKo ⟨1, (KX X).one_mem⟩
  have hcl : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    isClosed_stabT' X.B.I.cm.sig X.B.I.J (Af X.B.I.F) (tupH (frameOf X u))
  have hbT : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ ⊤ :=
    (h2.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK X).1)).ne
  have ha : 0 < ((X.measW u).μHinf Set.univ).toReal := ENNReal.toReal_pos ha0 haT
  have hb' : 0 < ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal :=
    ENNReal.toReal_pos hb0 hbT
  unfold MassAt
  rw [hcov, hU, hV, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (massH_nonneg X u)]
  field_simp

end MassDataMassesW
