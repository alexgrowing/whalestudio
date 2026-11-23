import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NarrowLemmaOfCrystallineLubinTate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTateCrystallineOfLocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTateCharacterContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTateFiltrationJumpAtEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleEmbeddingLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConjugateNotMemFiltrationOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantPeriodFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaEigenvaluesOfHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeLAdicCharacterAboveOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
import Development.AutomorphicArithmetic.ThetaCorrespondence.GaloisRepresentations.HeckeDeRham
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL
open GlobalTheory GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Inp

theorem pst : GlobalTheory.Published.DeRhamPotSemistable := GlobalTheory.deRham_potentiallySemistable

theorem alg : GlobalTheory.Published.AlgebraicCharacterWD :=
  UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds UpperTheory.Lit.heckeLAdicCharacterDeRham pst

theorem crys : GlobalTheory.Published.HeckeLAdicCharacterCrystalline := by
  have hD := UpperTheory.Lit.heckeLAdicCharacterDeRham
  have hB := pst
  have hW := alg
  intro E Ω _ _ _ _ _ l _ P AI hT ι art ha χ n μ h1 h2 h3 w A h O _ _ _ Bw hj hu
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := ParamAboveModel.isComp_loc (w := w) χ
  have hc : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    have e : (fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      (((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) => ((μ g : (Om l)ˣ) : Om l) := by
      funext g
      rw [Subsingleton.elim i j]
      simp [rk1]
    rw [e]
    exact Units.continuous_val.comp (h2.comp continuous_subtype_val)
  have hr := DeRhamPotSemistable.isPstAt hB hT.some Bw _ hc (hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj).1
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr,
    hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha',
    GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
  exact (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu

theorem hk : GlobalTheory.Published.HeckeLAdicCharacterAbove :=
  GlobalTheory.HeckeAboveBridge.heckeLAdicCharacterAbove_of_potSemistable UpperTheory.Lit.heckeLAdicCharacterDeRham crys pst

end UpperTheory.Gal.Int.Inp
