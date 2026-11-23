import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem charPol_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (LL : FinExt l)
    {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) (g : ↥(Weil h)) :
    haveI := hV.finite
    (wdPst P ι Bw h hj ρ).charPol g = (wdRho P ι Bw h hj ρ g).charpoly := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  exact (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq g

theorem UpperTheory.Gal.crystallineComparison.wdModel_of :
    WdModel := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hV g
  have key : wdAt P ι Bw h hj r = wdPst P ι Bw h hj (Bw.repE LL r') := by
    obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj (r := r) ⟨LL, r', hm, hV⟩
    have h₁ : L₁.1 ≤ (supExt L₁ LL).1 := le_sup_left
    have h₂ : LL.1 ≤ (supExt L₁ LL).1 := le_sup_right
    have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
        mapRep (IntermediateField.inclusion h₂).toRingHom r' := by
      ext x i j
      exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f x : Matrix (Fin a) (Fin a) (Om l)) i j)
        (hm₁.2.trans hm.2.symm)
    rw [e₁, GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₁ r₁ hV₁,
      GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₂ r' hV, e]
  refine ⟨?_, ?_⟩
  · rw [key]
    exact charPol_wdPst P ι h Bw hj LL (Bw.repE LL r') hV g
  · exact (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL _ _ hV).trans (by simp)
