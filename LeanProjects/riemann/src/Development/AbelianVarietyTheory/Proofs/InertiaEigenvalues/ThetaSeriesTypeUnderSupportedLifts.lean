import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeSupportLift

variable {D : D7}

theorem exists_isBaseFrame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsFrame β Λ) (h : IsSelfDualC V Λ) :
    ∃ N, Lev.IsBaseFrame V β Λ N := by
  obtain ⟨_, N, hB⟩ := GlobalTheory.FinAdIdent.exists_baseFrame V Λ h
  exact ⟨N, hβ, hB.2⟩

theorem idem_add_conj_mul {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    (idem P + cA D (idem P)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have e1 : idem P * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hP.mul_eq_zero hq hPP fun e => hne e.symm)
      (fun h => absurd hPP h)]
    exact (hP.isIdemAt hPP).1.1
  have e2 : idem P * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hP.mul_conj hq hPP
  have e3 : cA D (idem P) * idemAt PP = 0 := by
    rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hP.mul_conj hPP hq
  have e4 : cA D (idem P) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, e1]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, add_zero, zero_add]

theorem suppAt_idem_of_mem {V : HSp D} {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    {g : GA D V} (hg : SuppAt (idemAt PP) V g) : SuppAt (idem P) V g := fun i j => by
  rw [← hg i j, ← mul_assoc, idem_add_conj_mul hP hPP]

theorem exists_lift_supp {S T : HSp D} (B : Base S T) (hB : B.Good) (u : G0 B.G.Pg T.rank) :
    ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ := by
  obtain ⟨N, hN⟩ := exists_isBaseFrame hB.frame.frT hB.frame.sdT
  obtain ⟨R, h1, -, hR⟩ := hB.places.split
  have hPg : SplitSet B.G.Pg := hR.mono h1
  obtain ⟨e, κ, hl, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod T B.F.βT B.G.levT B.F.ΛT N hN
    (fun PP hP PP' hP' => by
      rcases hP' with hP' | hP'
      · exact GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (h1 hP')
      · exact absurd hP' (Finset.notMem_empty _))
    (Finset.disjoint_empty_right _) u
  refine ⟨_, (hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)).1, ?_⟩
  refine List.prod_induction _ (fun a b ha hb => GlobalTheory.SplitLinear.suppAt_mul ha hb) (GlobalTheory.SplitLinear.suppAt_one _ _) ?_
  intro x hx
  obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hx
  have hs := (hl PP).2.1
  rw [← idemAt_eq (hl PP).1] at hs
  exact suppAt_idem_of_mem hPg PP.2 hs

open Classical in

theorem series_type_supp : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω →
    ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧
      SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q →
        ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T),
          series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  intro D S T B hB hS ω hω u hu
  obtain ⟨κ, hκ, hs⟩ := exists_lift_supp B hB u
  refine ⟨κ, hκ, hs, fun Q hQ φ h P g => ?_⟩
  have hred : ∀ PP : ↥Q, redFn B.F.βT PP.1 (Lev.finE T κ) = 1 := fun PP =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT (GlobalTheory.ExportSeries.DualType.dualTypePlaces_isSplitNonconjugate_of_admissible hQ) Finset.subset_union_left
      (Finset.mem_union_right _ (Finset.mem_union_right _ PP.2))
      (fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ PP.2)) (parLev_St hκ.2.1) hs
  have := GlobalTheory.ExportType.series_type hB hS hQ hω hu (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ) (φ := φ) (φ' := φ) (fun _ => 1)
    (fun PP y => by rw [hred PP, Units.val_one, Matrix.one_mul, Units.val_one, one_mul]) h P g
  rw [this, Finset.prod_const_one, inv_one, mul_one]

end GlobalTheory.TypeSupportLift

end
