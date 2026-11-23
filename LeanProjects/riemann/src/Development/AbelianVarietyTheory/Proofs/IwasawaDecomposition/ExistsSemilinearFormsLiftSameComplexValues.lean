import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC.LiftExt

open Formalism.L2.Col in
set_option maxHeartbeats 1000000 in

private theorem liftHom_reidx (X : Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam₁ lam₂ : X.Tau → DomWeight n)
    (hl : lam₂ = lam₁) {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : LevFam X.E X.K n SG₁) (Λ₂ : LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ Lf : (formGSD (roundPk X lam₁ fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).EqFun →+
      (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₂
          fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ₂).EqFun,
      (∀ (a : X.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((Lf ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst lam₂
  subst SG₂
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have hmem : ∀ ψ : (formGSD (roundPk X lam₁ fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).EqFun,
      (fun d => hfsJ ι lam₁ (ψ.1 d)) ∈ (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₁
          fun d : DecoSet X.E n ∅ SG₁ => d.1.N) (Λ₁.coefMap ι)).EqFun := by
    intro ψ
    obtain ⟨φ₂, h⟩ := GlobalTheory.Mem.R3.Tr.levelFamily_coefficientChange_liftRound X ι e he lam₁ Λ₁ (Λ₁.coefMap ι) (fun w => rfl)
      (fun w h₁ h₂ hh => by
        have : h₁ = h₂ := Subtype.ext hh
        subst this
        rfl) ψ
    have : (fun d => hfsJ ι lam₁ (ψ.1 d)) = φ₂.1 := funext fun d => Subtype.ext (h d).symm
    rw [this]
    exact φ₂.2
  refine ⟨{ toFun := fun ψ => ⟨fun d => hfsJ ι lam₁ (ψ.1 d), hmem ψ⟩, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Subtype.ext
    funext d
    exact map_zero _
  · intro ψ χ
    apply Subtype.ext
    funext d
    exact map_add _ _ _
  · intro a ψ
    apply Subtype.ext
    funext d
    exact hfsJ_smul ι lam₁ a (ψ.1 d)
  · intro ψ d₁ d₂ hd
    cases hd
    apply heq_of_eq
    show MvPolynomial.map c₂ (MvPolynomial.map ι (ψ.1 d₁).1) = _
    rw [MvPolynomial.map_map]
    have hc' : c₂.comp ι = c₁ := RingHom.ext hc
    rw [hc']

open Formalism.L2.Col in

private theorem formsLift_of_eqFunLift {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [StarRing K₁] [Field K₂] [NumberField K₂] [StarRing K₂]
    (ι : K₁ →+* K₂) (S₁ : GSD K₁) (S₂ : GSD K₂) (h₁ : S₁.Ok) (h₂ : S₂.Ok) (Lf : S₁.EqFun →+ S₂.EqFun)
    (hLf : ∀ (a : K₁) ψ, Lf (a • ψ) = ι a • Lf ψ) :
    ∃ L : (S₁.toCSD h₁).Forms →+ (S₂.toCSD h₂).Forms, (∀ (a : K₁) f, L (a • f) = ι a • L f) ∧
      ∀ f, (S₂.res h₂).symm (L f) = Lf ((S₁.res h₁).symm f) := by
  refine ⟨(S₂.res h₂).toLinearMap.toAddMonoidHom.comp (Lf.comp (S₁.res h₁).symm.toLinearMap.toAddMonoidHom),
    fun a f => ?_, fun f => ?_⟩
  · show S₂.res h₂ (Lf ((S₁.res h₁).symm (a • f))) = ι a • S₂.res h₂ (Lf ((S₁.res h₁).symm f))
    rw [map_smul, hLf, map_smul]
  · show (S₂.res h₂).symm (S₂.res h₂ (Lf ((S₁.res h₁).symm f))) = _
    exact LinearEquiv.symm_apply_apply _ _

set_option maxHeartbeats 4000000 in

private theorem eqFun_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x) :
    ∃ Lf : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).EqFun →+ (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').EqFun,
      (∀ (a : B.fields.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((Lf ψ).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hj
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have ef : f' = f := eq_of_heq hf
  have ep : w'.px = w.px := eq_of_heq hpx
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hι' : ∀ x, (baseOfColW w').embLL (ι x) = (baseOfColW w).embLL x := hι
  refine liftHom_reidx (baseOfColW w).fields ι (baseOfColW w').tauLL ?_ _ _ rfl ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hι
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hι' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' W').trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w W).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w W) (twistRamifiedPrimes_empty_colTuples w' W') _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of ι p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    refine Eq.trans ?_ (hι' _).symm
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    have eC : w'.I.C = w.I.C := w'.C_eq.trans (ef.trans w.C_eq.symm)
    rw [eC] at e1
    exact e1.trans e2.symm

set_option maxHeartbeats 4000000 in

private theorem forms_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').Ok) :
    ∃ L : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms →+ (Formalism.L2.Col.GSD.toCSD _ h₂).Forms,
      (∀ (a : B.fields.K) ψ, L (a • ψ) = ι a • L ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm (L ψ)).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm ψ).1 d).1) := by
  obtain ⟨Lf, hs, hc⟩ := eqFun_lift w w' W W' hpre hf hpx j j' hj ι hι
  obtain ⟨L, hL, hr⟩ := formsLift_of_eqFunLift ι _ _ h₁ h₂ Lf hs
  refine ⟨L, hL, fun ψ d d' hd => ?_⟩
  rw [hr]
  exact hc _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC.LiftExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) ∧ (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  exact GlobalTheory.Mem.R3.DefLatBC.LiftExt.forms_lift w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hf hp ((j : ℕ) + 1) ((j' : ℕ) + 1)
    (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
