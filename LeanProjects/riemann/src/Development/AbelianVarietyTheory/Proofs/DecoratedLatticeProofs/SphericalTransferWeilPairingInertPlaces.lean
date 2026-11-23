import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmallerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegmentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegmentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

set_option maxHeartbeats 1000000 in

theorem transferOn_inert : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun v => ¬ IsSplit (E := D.host.E) v := by
  intro hH D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hbne
  obtain ⟨hS, hT⟩ := hunr w h
  rcases hx with ⟨hs, -⟩ | ⟨hin, c, ϖ, eS, α, hUI, heS, hxS, rfl⟩
  · exact absurd hs hv
  obtain ⟨-, hodd, hch⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).2 hv
  obtain ⟨eT, heT⟩ := hch c heS.1
  have hf0 : (f : WO S T → ℂ) ≠ 0 := fun h0 => hbne (by rw [show f = 0 from Subtype.ext h0]; simp)
  obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, hcT, hcS⟩ :=
    GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hUI heS heT f hf hf0
  have hq0 : (qV D.host.F v : ℂ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  obtain ⟨hvS, hsegS⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS
  obtain ⟨hvT, -⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χT T.rank hW.hecT hW.resT v w h hin hT
  refine Or.inr ⟨hin, c, ϖ, eT, liftPar (Units.mk0 _ hq0) S.rank T.rank α, hUI, heT, ?_, ?_⟩
  · set α' := liftPar (Units.mk0 _ hq0) S.rank T.rank α
    have e1S : embV S v (eS.symm 1) = 1 := by rw [map_one, map_one]
    have e1T : embV T v (eT.symm 1) = 1 := by rw [map_one, map_one]
    have e0S : embV S v 1 = 1 := map_one _
    have e0T : embV T v 1 = 1 := map_one _
    obtain ⟨RS, hRS⟩ : ∃ RS : Representation ℂ (GU c S.rank) (WO S T → ℂ),
        ∀ g u, RS g u = om (embV S v (eS.symm g), 1) u :=
      ⟨om.comp ((MonoidHom.inl _ _).comp ((embV S v).comp eS.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨RT, hRT⟩ : ∃ RT : Representation ℂ (GU c T.rank) (WO S T → ℂ),
        ∀ g u, RT g u = om (1, embV T v (eT.symm g)) u :=
      ⟨om.comp ((MonoidHom.inr _ _).comp ((embV T v).comp eT.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨πS, hπS⟩ : ∃ πS : Representation ℂ (GU c S.rank) U, ∀ g (u : U), ((πS g u : U) : WO S T → ℂ) = RS g u :=
      ⟨GlobalTheory.PRep.sub RS U fun g u hu => by rw [hRS, ← e0T]; exact hU _ _ u hu, fun _ _ => rfl⟩
    obtain ⟨πT, hπT⟩ : ∃ πT : Representation ℂ (GU c T.rank) U, ∀ g (u : U), ((πT g u : U) : WO S T → ℂ) = RT g u :=
      ⟨GlobalTheory.PRep.sub RT U fun g u hu => by rw [hRT, ← e0S]; exact hU _ _ u hu, fun _ _ => rfl⟩
    have hMS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = RS g m := fun g m => by
      rw [hRS, hωom, e1T]
    have hMT : ∀ g (m : M), ((ω (1, g) m : M) : WO S T → ℂ) = RT g m := fun g m => by
      rw [hRT, hωom, e1S]
    have hvac := hstd.2.2.1
    have hfixS : ∀ k ∈ KU c S.rank, πS k f = f := fun k hk => by
      have a4 := hstd.1.fix k 1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 (one_mem _) s hvac
      apply Subtype.ext
      rw [hπS, ← hsf, ← hMS]; exact congrArg Subtype.val a4
    have hfixT : ∀ k ∈ KU c T.rank, πT k f = f := fun k hk => by
      have a4 := hstd.1.fix 1 k (one_mem _) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 s hvac
      apply Subtype.ext
      rw [hπT, ← hsf, ← hMT]; exact congrArg Subtype.val a4
    have hcom1 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI S.rank
    have hcom2 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI T.rank
    have hρ1 : ρ 1 x = x := by rw [map_one]; rfl
    have hbT : ∀ g (u : U), b (πT g u) x = ρ' (eT.symm g) (b u x) := fun g u => by
      have e2 := hb 1 (eT.symm g) u x
      have e : πT g u = ⟨om (embV S v 1, embV T v (eT.symm g)) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπT g u).trans ((hRT g u).trans (congrArg (fun z => om (z, embV T v (eT.symm g)) (u : WO S T → ℂ)) e0S.symm)))
      rw [hρ1] at e2
      rw [e, e2]
    have hbS : ∀ g (u : U) y, b (πS g u) (ρ (eS.symm g) y) = b u y := fun g u y => by
      have e2 := hb (eS.symm g) 1 u y
      have e : πS g u = ⟨om (embV S v (eS.symm g), embV T v 1) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπS g u).trans ((hRS g u).trans (congrArg (fun z => om (embV S v (eS.symm g), z) (u : WO S T → ℂ)) e0T.symm)))
      rw [map_one ρ', Module.End.one_apply] at e2
      rw [e, e2]
    refine ⟨hbne, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h' hh' => ?_⟩
    · show ρ' (eT.symm k) (b f x) = b f x
      rw [← hbT, hfixT k hk]
    · have : CharZero (w.adicCompletion D.host.E) :=
        charZero_of_injective_algebraMap (algebraMap D.host.E (w.adicCompletion D.host.E)).injective
      obtain ⟨h0, hh0, heq⟩ := GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller hH _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd h' hh'
      have hsat := GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd hcT hcS (by omega) h0 hh0 h' hh' heq
        (Units.mk0 _ hq0) rfl α
      have sA : b (heckeVec πT (KU c T.rank) h' f) x =
          heckeVec (ρ'.comp eT.symm.toMonoidHom) (KU c T.rank) h' (b f x) :=
        map_heckeVec hcom2.1 hh' (b.flip x) (fun g u => hbT g u) f
      have sB : heckeVec πT (KU c T.rank) h' f = heckeVec πS (KU c S.rank) h0 f := by
        apply Subtype.ext
        have m1 := map_heckeVec hcom2.1 hh' U.subtype (ρ' := RT) (fun g u => hπT g u) f
        have m2 := map_heckeVec hcom2.1 hh' M.subtype (ρ := ω.comp (MonoidHom.inr _ _)) (ρ' := RT) (fun g m => hMT g m) s
        have m3 := map_heckeVec hcom1.1 hh0 M.subtype (ρ := ω.comp (MonoidHom.inl _ _)) (ρ' := RS) (fun g m => hMS g m) s
        have m4 := map_heckeVec hcom1.1 hh0 U.subtype (ρ' := RS) (fun g u => hπS g u) f
        simp only [Submodule.subtype_apply] at m1 m2 m3 m4
        rw [m1, m4, ← hsf, ← m2, ← m3, heq]
      have sC := (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear (GU c S.rank) (KU c S.rank) hcom1.1 hcom1.2.1 U X X' πS (ρ.comp eS.symm.toMonoidHom) b
        (fun g u y => hbS g u y) f (GlobalTheory.LGrp.mem_fixed.2 hfixS) x hxS.2.1 h0 hh0).2
      have hev : (fun g => h0 g⁻¹) = h0 := funext fun g => hcom1.2.2 h0 hh0 g
      rw [← sA, sB, sC, hev, hxS.2.2 h0 hh0, map_smul, hsat]
  · have hc := GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment (Units.mk0 _ hq0) S.rank T.rank (by omega) α
    have ht' : ((T.rank : ℤ) - S.rank) = (t : ℤ) := by omega
    rw [ht'] at hc
    have e := congrArg (Multiset.map (((-1 : ℂˣ) ^ S.rank) * ·)) hc
    simp only [Multiset.map_map, Multiset.map_add, Function.comp_def, mul_inv_cancel_left] at e
    rw [Multiset.map_id'] at e
    rw [e, stepPar, hvS, hvT, hsegS (Units.mk0 _ hq0) _ t rfl]
    congr 1
    · exact Multiset.map_congr rfl fun y _ => by group

end GlobalTheory.ChainOnto

end
