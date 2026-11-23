import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanOfMemMof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumOverDataTermCountEqLatticeMassStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem M_eq_Mof (S : Frames L r k) {C : Set S.FrP} {p : S.FrP} (hp : p ∈ C) {d : S.Datum}
    {Λ : Submodule L.O S.V} (hC : S.Fr d Λ = C) : S.M d Λ = S.Mof p.1 p.2 := by
  subst hC
  exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1 p hp).2.symm

theorem class_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, (∀ Q : ℕ → Prop, (S.sumData fun d => S.nT d C fun Λ => Q (S.be d Λ)) ≤ ∑' Mh : {Mh : Submodule L.O S.V // S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) ∧ Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup)}, S.massSig Mh) ∧ (S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ) = S.massSig (S.Mof p.1 p.2) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp
  have hM : ∀ d Λ, S.Fr d Λ = C → S.M d Λ = S.Mof p.1 p.2 := fun d Λ hF => M_eq_Mof S hp hF
  constructor
  · intro Q
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => Q (S.be d Λ)) ?_).trans_le ?_
    · intro h hh d Λ hT hQ
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show Q (S.be (h • d) (h • Λ))
      unfold Frames.be
      rw [hM', hsat']
      exact hQ
    · unfold Frames.massSig
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun o => ?_
      split_ifs with hcond
      · obtain ⟨d, hT, hQ, hF⟩ := hcond
        have hbasic := GlobalTheory.HL.TermBasic.term_basic L r k S d o.out hT
        have hSD : IsSD L S.Hm o.out := hbasic.1
        have hle : S.M d o.out ≤ S.sat o.out := hbasic.2.2.1
        rw [hM d o.out hF] at hle
        have hQ' : Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex (S.sat o.out).toAddSubgroup) := by
          have h := hQ
          unfold Frames.be at h
          rw [hM d o.out hF] at h
          exact h
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨S.sat o.out, hle,
          fun x hx => (Submodule.mem_inf.mp hx).2,
          fun x hx y hy => (hSD.2 y).mpr (Submodule.mem_inf.mp hy).1 x (Submodule.mem_inf.mp hx).1, hQ'⟩)
        rw [if_pos ⟨hSD, rfl⟩]
      · exact zero_le
  · have hb : ∀ Λ : Submodule L.O S.V, (∃ d, S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C) ↔
        (IsSD L S.Hm Λ ∧ S.sat Λ = S.Mof p.1 p.2) := by
      intro Λ
      constructor
      · rintro ⟨d, hT, hB, hF⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1,
          (show S.M d Λ = S.sat Λ from hB).symm.trans (hM d Λ hF)⟩
      · rintro ⟨hSD, hsat⟩
        obtain ⟨d, hT, hF, hB⟩ := GlobalTheory.HL.PrimTerm.term_of_primitive L r k S Λ hSD C hC p hp hsat
        exact ⟨d, hT, hB, hF⟩
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => S.BBzero d Λ) ?_).trans ?_
    · intro h hh d Λ hT hB
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show S.M (h • d) (h • Λ) = S.sat (h • Λ)
      rw [hM', hsat']
      exact hB
    · unfold Frames.massSig
      exact tsum_congr fun o => if_congr (hb o.out) rfl rfl

end GlobalTheory.HL.ClassMass
