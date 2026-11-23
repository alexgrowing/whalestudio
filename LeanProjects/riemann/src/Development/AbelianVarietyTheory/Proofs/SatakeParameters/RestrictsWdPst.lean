import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusSemisimplificationWeilDeligneRestrictsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

theorem restricts_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) {K L Ω : Type} [Field Ω] [Field K]
    [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
    [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {O O' : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw)
    (hj' : GlobalTheory.Pst.Induces Bw') (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1) {LL : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) :
    Restricts (wdPst P ι Bw h hj ρ) (wdPst P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle)) := by
  have hV' := (GlobalTheory.PstLaws.isPst_resTo_iff P ρ hle).2 hV
  haveI := hV.finite
  haveI := hV'.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV']
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv l P ι K L Ω A v v' h h' O O' Bw Bw' hj hj' hle
    (fun σ σ' hσ => weilToGK_eq Bw Bw' hjj hle h h' σ σ' hσ) LL V ρ hV
  exact GlobalTheory.T.frobeniusSemisimplification_weilDeligne_restricts K L Ω A v v' h h' _ _ _ _ _ _ _ _ (isSmooth_wdRho P ι Bw h hj ρ)
    (isSmooth_wdRho P ι Bw' h' hj' _) (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' _) e he1 he2

theorem wdAt_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj' : GlobalTheory.Pst.Induces Bw'), IsPstAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) ∧ Restricts (wdAt P ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (wdAt P ι Bw' h' hj' ((resTo L r).comp (Dec (F := L) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι P AI _ a r O _ _ _ Bw hj hr
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨S, Bw', hjj, hS, hle⟩ := exists_bridge (L := L) Bw hj L₁
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  have key : ∀ (T : FinExt l) (hT : L₁.1 ≤ T.1), mapRep (algebraMap ↥T.1 (Om l))
      ((mapRep (IntermediateField.inclusion hT).toRingHom r₁).comp (decRes A)) =
      (GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype := by
    intro T hT
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₁.2
  have hpS : IsPst P (Bw'.repE Bw'.LL ((mapRep (IntermediateField.inclusion hS).toRingHom r₁).comp (decRes A))) := by
    rw [repE_decRes Bw Bw' hjj hle]
    exact (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).2 (GlobalTheory.PstExt.isPst_enlarge P Bw hS r₁ hV₁)
  have hrL : IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) :=
    ⟨Bw'.LL, _, ⟨le_rfl, key Bw'.LL hS⟩, hpS⟩
  refine ⟨_, _, _, _, Bw', hj', hrL, ?_⟩
  obtain ⟨L₃, r₃, hm₃, hV₃, e₃⟩ := wdAt_of_isPstAt ι Bw' h' hj' hrL
  have h13 : L₁.1 ≤ (supExt L₁ L₃).1 := le_sup_left
  have h33 : L₃.1 ≤ (supExt L₁ L₃).1 := le_sup_right
  have hm₃' : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) (supExt L₁ L₃)
      (mapRep (IntermediateField.inclusion h33).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h33, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw' _ hm₃' ⟨hm₃.1.trans h33, key _ h13⟩
  rw [e₁, e₃, BridgeParam.wdPst_enlarge P ι Bw h hj h13 r₁ hV₁, BridgeParam.wdPst_enlarge P ι Bw' h' hj' h33 r₃ hV₃,
    heq, repE_decRes Bw Bw' hjj hle]
  exact restricts_wdPst P ι h h' Bw Bw' hj hj' hjj hle _ (GlobalTheory.PstExt.isPst_enlarge P Bw h13 r₁ hV₁)

end GlobalTheory.AboveLRes
