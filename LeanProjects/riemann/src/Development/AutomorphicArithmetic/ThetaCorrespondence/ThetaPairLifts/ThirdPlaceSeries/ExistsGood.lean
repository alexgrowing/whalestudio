import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPoint

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller
namespace UpperTheory.GalC
attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk
theorem exists_good_alt (hCen : ∀ (D : D7) (_ : PairedCharacterCondition.Pend D), GlobalTheory.Pass.CentralElt D) {D : D7} {nch : NChoice D} (hP : _root_.UpperTheory.GalC.GaloisPreconditions D nch)
    (hT : Tie4 D) : ∃ c : CutD D, c.Good := by
  classical
  obtain ⟨-, ⟨Q, hDZ, hEig⟩, -, hSer⟩ := hT
  have h0 : SumRepresentations.tie0 D := hP.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := hP.adm.1.1.2.2.1
  have h5 : SumRepresentations.adm5 D := hP.adm.1.1.2.2.2.2.2.2
  have h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D := hP.Conclusion1.1
  let Xs : ∀ i, Set (D.nd.X i) := fun i => {x | ∃ PI, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F ≠ 0}
  have hZ : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ D.nd.Z i := fun i x hx => (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
  have hgood : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ Xs i := fun i x hx => by
    obtain ⟨PI, hPI⟩ := D.naut.pt_surj i x
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i PI)
    exact ⟨PI, hPI, F, hF, by
      rw [(_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx]; exact hF0⟩
  refine ⟨⟨fun i => (D.nd.Zgood i).Nonempty, Xs, fun i ⟨x, hx⟩ => ⟨x, hgood i x hx⟩⟩,
    fun _ => Iff.rfl, hgood, fun i x hx ⟨PI, hPI, F, hF, hne⟩ => ?_, fun i _ => ?_, fun i _ P x ⟨PI, hPI, F, hF, hne⟩ hx k w hw => ?_⟩
  · by_contra hxg
    exact hne ((_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg)
  · obtain ⟨z, hact⟩ := exists_unit_one_add_generator D (hCen D Q) i
    refine ⟨Q.zO i z, Q.zO_comm i z, fun x hx u hu => ?_, fun x hx u hu => ?_⟩
    · have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
        rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx, map_natCast]) u hu
      rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
    · have := hEig i z x 0 (fun PI hPI F hF => by
        have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0 := by
          by_contra hne
          exact hx ⟨PI, hPI, F, hF, hne⟩
        rw [hact, e, smul_zero, map_zero, zero_smul]) u hu
      rw [this, zero_smul]
  · obtain ⟨s, hg, hs⟩ := exists_tuple D _ _ F hne
    have hn := nc_of_type D Q hDZ h1 h0 i PI hg (fun k v => exists_type D Q i PI F hF k v _ (hs k v)) k w hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨Pa', hB'⟩ := h1 i P
    have hperm : Pa.Perm Pa' := ((h41 i).2.1 PI P (by rw [hPI]; exact Option.some_ne_none x)
      (hPI.trans hx.symm)).1 Pa Pa' hB hB'
    have hB2 := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB'
    have hsp := GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw
    rwa [← hB.2.2.2.1 w hsp, hB2.2.2.2.1 w hsp] at hn
end UpperTheory.GalC
end
end
