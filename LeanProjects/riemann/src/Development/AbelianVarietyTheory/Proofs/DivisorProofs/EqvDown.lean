import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperatoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem lawsLL : GlobalTheory.UT.LL :=
  ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1, GlobalTheory.allSixLaws.2.2.2.2.1⟩

theorem eqv_down : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab' E',
    LabExt em lab lab' → Eqv D.toPre A F N lab' E' → ∃ E, Eqv D.toPre A (Kb R) N lab E := by
  intro R _ _ _ hB D A N hN lab F _ _ _ em lab' E' hL hE
  obtain ⟨hAdm, hC⟩ := hB
  have hN1 : 1 ≤ N := hN.pos
  have honto := GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field R D.toPre A N hN1 lab F em lab' hL hE.onto
  have hframe : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (p : QkPt D.toPre K N),
      ∃ w, GlobalTheory.UT.TXFrame N p w := fun K _ _ _ p =>
    (GlobalTheory.UT.SymFrame.main lawsLL R (maximalIdeal R) hAdm D K N hN p).1
  let J := {q : (p : QkPt D.toPre (Kb R) N) × GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b ×
      ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R)) // GlobalTheory.UT.TXFrame N q.1 q.2.1 ∧ SymLift A.A A.L N N (lab q.1) q.2.2}
  choose a ha using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D (Kb R) N hN i.1.1 i.1.2.1 i.2.1
  choose b hb using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A (Kb R) N i.1.2.2
  have hq := (GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1).1
  choose p' hp' using fun i : J => (hq i.1.1).exists
  choose w' hw' using fun i : J => hframe F (p' i)
  have hlab : ∀ i : J, lab' (p' i) = baseEm em ≫ lab i.1.1 := fun i =>
    Over.OverMorphism.ext (by rw [hL _ _ (hp' i)]; rfl)
  choose θ' hθ' using fun i : J =>
    GlobalTheory.WeightProbe.exists_symLift_top A hN (lab' (p' i)) ((hE.onto _).2 ⟨_, rfl⟩)
  choose a' ha' using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D F N hN (p' i) (w' i) (hw' i)
  choose b' hb' using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A F N (θ' i)
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  haveI : FiniteDimensional F (Fam D.toPre F N) :=
    (GlobalTheory.UU.finrank_fam_of_laws GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 R D.toPre D.tau_bimult F N hN1).1
  have hfamExt : GlobalTheory.FieldBaseChange.IsExtension (famExt D.toPre em N) :=
    GlobalTheory.FieldBaseChange.isExtension_famPull D.toPre (Kb R) F _ hN1
  have hsecExt := GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange R A F em N
  have ca : ∀ i v, a' i (famExt D.toPre em N v) = famExt D.toPre em N (a i v) := fun i v =>
    ((ha' i _ _).1 (GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension R (maximalIdeal R) hAdm D F em N hN i.1.1 i.1.2.1 (p' i) (w' i) i.2.1 (hw' i) (hp' i) v _
      ((ha i v _).2 rfl))).symm
  have cb : ∀ i t, b' i (secExt A em N t) = secExt A em N (b i t) := fun i t =>
    ((hb' i _ _).1 (GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension R A F em N hN (lab i.1.1) i.1.2.2 (θ' i) i.2.2 (by rw [← hlab i]; exact hθ' i) t _
      ((hb i t _).2 rfl))).symm
  let E'' : Fam D.toPre F N →ₗ[F] SecF A F N :=
    { toFun := E'
      map_add' := fun s t => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j =>
        hE.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl) j }
  have cE : ∀ i v, E'' (a' i v) = b' i (E'' v) := fun i v =>
    (hb' i _ _).1 (hE.act (p' i) (w' i) (θ' i) v (a' i v) (hw' i) (hθ' i) ((ha' i v _).2 rfl))
  obtain ⟨E, hEb, hEc⟩ := GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange (Kb R) F _ _ _ _ (famExt D.toPre em N) (secExt A em N) hfamExt hsecExt J a b a' b'
    ca cb E'' hE.bij cE
  refine ⟨fun s => E s, ⟨hEb, ?_, ?_, honto, hframe (Kb R),
    fun p => GlobalTheory.WeightProbe.exists_symLift_top A hN (lab p) ((honto _).2 ⟨p, rfl⟩), ?_⟩⟩
  · intro s s' s'' h j
    have : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext h
    subst this
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_add E s s')
  · intro c s s' h j
    rw [(ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h]
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_smul E c s)
  · intro p w θ s s' hw hθ hP
    let i : J := ⟨⟨p, w, θ⟩, hw, hθ⟩
    have e1 : s' = a i s := (ha i s s').1 hP
    have e2 : E s' = b i (E s) := by rw [e1]; exact hEc i s
    exact (hb i (E s) (E s')).2 e2

end GlobalTheory.Mum.Desc
