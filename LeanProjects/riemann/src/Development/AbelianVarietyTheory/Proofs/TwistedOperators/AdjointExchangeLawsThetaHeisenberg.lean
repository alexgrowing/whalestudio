import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ExchPf

open GlobalTheory.PairLift GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

def withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) : HSp D :=
  { V with hT := h, herm := e ▸ V.herm, nondeg := e ▸ V.nondeg, baseLattice_isUnimodular := e ▸ V.baseLattice_isUnimodular }

theorem HR_withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) :
    HR (AF D.host.F) D.sp.cm.sig V.gram = HR (AF D.host.F) D.sp.cm.sig (withForm V h e).gram := by
  subst e; rfl

theorem datum_withForm {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (h : B.V →ₗ⋆[D.host.E] B.V →ₗ[D.host.E] D.host.E) (e : h = B.hT)
    (ω : GA D A × GA D (withForm B h e) →* Module.End ℂ (WO A (withForm B h e) → ℂ))
    (hd : IsWeilDatumO ψ A (withForm B h e) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap (MulEquiv.subgroupCongr (HR_withForm B h e)).toMonoidHom)) := by
  subst e
  exact hd

theorem datum_negneg {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (ω : GA D A × GA D (negSp (negSp B)) →* Module.End ℂ (WO A (negSp (negSp B)) → ℂ))
    (hd : IsWeilDatumO ψ A (negSp (negSp B)) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap ((negGA B).trans (negGA (negSp B))).toMonoidHom)) := by
  have key := datum_withForm (ψ := ψ) (A := A) (B := B) (χ := χ) (χ' := χ') (-(-B.hT)) (neg_neg _) ω hd
  have e : ((negGA B).trans (negGA (negSp B))).toMonoidHom =
      (MulEquiv.subgroupCongr (HR_withForm B (-(-B.hT)) (neg_neg _))).toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [e]
  exact key

theorem exch_eq_cj (A B : HSp D) (f : WO A B → ℂ) : exch A B f = cj id (dag A B f) := by
  funext x; simp [GlobalTheory.CoreOnto.exch, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag]

theorem theta_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (f : WO A B → ℂ) :
    IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  rw [exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).1 (dag A B f)).2]
  exact ⟨hAB.theta f, fun h => by simpa only [GlobalTheory.WeilConj.dag_dag hAB] using hBA.theta _ h⟩

theorem heis_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x : WO (negSp B) A)
    (f : WO A B → ℂ) : heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  rw [exch_eq_cj, exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).2 x (dag A B f)).2, hAB.Heisenberg₂]

theorem sympl_negB (A B : HSp D) (x x' : WO B A) : symplO (negSp B) A x x' = -symplO B A x x' := by
  have e : hO (negSp B) A x x' = -hO B A x x' := by
    unfold hO
    rw [negSp_gram, GlobalTheory.CjNeg.inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem sympl_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x x' : WO (negSp B) A) :
    symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x') := by
  rw [(GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).sympl, sympl_negB]

theorem bij_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) :
    Function.Bijective (adjO A B) :=
  Function.bijective_iff_has_inverse.2 ⟨adjO B A, fun x => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A).invol x,
    fun y => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).invol y⟩

theorem covol_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    (m : Measure (Mx D B.rank A.rank)) (X : Set (Mx D B.rank A.rank)) (hX : IsCovolOne (ratL B A) m X) :
    ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧ ∀ f f' : WO A B → ℂ,
      ∫ w in X, f w * starRingEnd ℂ (f' w) ∂m = ∫ w in X', exch A B f w * starRingEnd ℂ (exch A B f' w) ∂m' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  obtain ⟨hμ, h𝓕, h1⟩ := hX
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank B.rank
  haveI : BorelSpace (WO A B) := ⟨rfl⟩
  haveI : BorelSpace (WO B A) := ⟨rfl⟩
  let eA : WO A B ≃+ WO B A :=
    { toFun := adjO B A
      invFun := adjO A B
      left_inv := fun x => hAB.invol x
      right_inv := fun y => hBA.invol y
      map_add' := hBA.add }
  let eH : WO A B ≃ₜ WO B A := ⟨eA.toEquiv, hBA.cont, hAB.cont⟩
  let eM : WO A B ≃ᵐ WO B A := eH.toMeasurableEquiv
  have hHaar : (m.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map m eA hBA.cont hAB.cont
  have hmp : MeasurePreserving eM m (m.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (m.map eM) m := MeasurePreserving.symm eM hmp
  let eG : ratL B A → ratL A B := fun g => ⟨adjO B A g, (hBA.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO A B g, (hAB.rat g).2 g.2⟩, Subtype.ext (hBA.invol g)⟩⟩
    have e := congrArg (fun x : ratL A B => adjO A B (x : WO B A)) hg
    simp only [eG, hAB.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL A B) (eM.symm ⁻¹' X) (m.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO A B (adjO B A g + x) = (g : WO A B) + adjO A B x
    rw [hAB.add, hAB.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' X) = X := by
    ext a; simp
  refine ⟨m.map eM, eM.symm ⁻¹' X, ⟨hHaar, hF, ?_⟩, fun f f' => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · symm
    rw [MeasurableEquiv.restrict_map, integral_map_equiv, hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (adjO A B (adjO B A x)) * starRingEnd ℂ (f' (adjO A B (adjO B A x))) = _
    rw [hAB.invol]

theorem weil_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ)) (hω : IsWeilDatumO ψ (negSp B) A χS χT ω) :
    ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  have h1 := GlobalTheory.ConjWeil.weil_conjSource D ψ (negSp B) A χS χT ω hω
  obtain ⟨ω₃, h3, R⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ (negSp (negSp B)) A χS⁻¹ χT⁻¹ (conjSource ω) h1
  refine ⟨_, datum_negneg ω₃ h3, fun f _ g h => ?_⟩
  have hadj : ∀ y : WO A B, adjO (negSp (negSp B)) A y = adjO B A y := by
    intro y; simp only [adjO, negSp_gram, neg_neg]
  have hf : dag (negSp (negSp B)) A (cj id (exch A B f)) = f := by
    funext y
    simp only [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, GlobalTheory.CoreOnto.exch, Complex.conj_conj, hadj, hAB.invol]
  have R' := R ((negGA (negSp B)) (negGA B h)) g (cj id (exch A B f))
  rw [hf] at R'
  show _ = exch A B (ω₃ (g, (negGA (negSp B)) (negGA B h)) f)
  rw [R', GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  funext x
  simp only [GlobalTheory.CoreOnto.exch, dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj, hadj, hBA.invol]

theorem exchLaw : ∀ D : D7, ExchLaw D := by
  intro D ψ A B hψ
  exact ⟨theta_exch hψ A B, heis_exch hψ A B, sympl_exch hψ A B, bij_exch hψ A B,
    fun m X hX => covol_exch hψ A B m X hX, fun χS χT ω hω => weil_exch hψ A B χS χT ω hω⟩

end GlobalTheory.ExchPf

end
