import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlargeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFrobeniusSemisimplificationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem wdPst_twist_one_field : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) = (wdPst P ι Bw h hj (Bw.repE L s)).lpChar (wdPst P ι Bw h hj (Bw.repE L m)) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m hs hm ht
  haveI := hs.finite
  haveI := hm.finite
  haveI := ht.finite
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.dpstLetter_twist_tensor_equiv P AI hT ι Bw h hj s m hs hm ht
  have f1 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L s)
  have f2 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L m)
  have f3 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
  have f12 := GlobalTheory.T.tensor_frobeniusSemisimplification f1 f2
  have hI := IsFrobSS.iso f12 f3 e (fun g v => he1 g v) (fun v => he2 v)
  rw [wdPst_of_isPst ι Bw h hj hs, wdPst_of_isPst ι Bw h hj hm, wdPst_of_isPst ι Bw h hj ht, WD.lpChar_mk]
  exact (WD.sound hI).symm

theorem wdAt_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r c _ _ hr hc ht
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₂, c₂, hm₂, hp₂, e₂⟩ := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L₃, t₃, hm₃, hp₃, e₃⟩ := wdAt_of_isPstAt ι Bw h hj ht
  have l₁ : L₁.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_left.trans le_sup_left
  have l₂ : L₂.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right.trans le_sup_left
  have l₃ : L₃.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right
  have hmt := isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂)
  have hu := IsModel.unique Bw (r := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) (hm₃.enlarge l₃) hmt
  have q₃ := GlobalTheory.PstExt.isPst_enlarge P Bw l₃ t₃ hp₃
  rw [hu] at q₃
  rw [e₁, e₂, e₃, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₃ t₃ hp₃, hu, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₁ r₁ hp₁, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₂ c₂ hp₂]
  exact wdPst_twist_one_field P AI hT ι Bw h hj _ _ (GlobalTheory.PstExt.isPst_enlarge P Bw l₁ r₁ hp₁)
    (GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂) q₃

end GlobalTheory.TwistParamAbove
