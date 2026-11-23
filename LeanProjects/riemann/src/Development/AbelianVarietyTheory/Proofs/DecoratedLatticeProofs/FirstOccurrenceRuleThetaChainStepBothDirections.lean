import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembersStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepRule

theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

theorem rulePar_step : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X →
    ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧
      RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  intro D X h3 h4 h5 k hk τ
  obtain ⟨al, be, ga, de, hd, hfar, e0, e1⟩ := hk τ
  have hT : ThetaPar D.R.t (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) (expT D k τ) (expS D k τ) :=
    ⟨al, be, ga, de, e0, Or.inl ⟨hd, e1⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom (expT D k τ) (((D.R.t : ℚ) + 3) / 2) (parA (Ptw D) k τ) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    rw [e0] at hs
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + expT D k τ := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩,
    rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inr hT⟩⟩

end GlobalTheory.StepRule

end
