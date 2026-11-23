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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem csum_res_symm {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (h : S.Ok)
    (f : (S.toCSD h).Forms) (c : S.Cl) :
    (((S.res h).symm f : S.EqFun) : S.D → S.V) (Quotient.out c) = (f.1 : S.Cl → S.V) c :=
  congrArg (fun u : (S.toCSD h).Forms => (u.1 : S.Cl → S.V) c) ((S.res h).apply_symm_apply f)

theorem csum_round_bc (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (hstar : ∀ x, ι (star x) = star (ι x))
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hH : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (Λ₂ ⟨w.1, hw⟩).H = (Λ₁ w).H)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x)
    (h₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).Ok)
    (h₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₂ => d.1.N) Λ₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hS
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨H₂, l₂, rfl⟩ : ∃ (H₂ : ∀ w : ↥SG₂, Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))) (l₂ : ∀ w, ↥(H₂ w) →* Lˣ),
      Λ₂ = fun w => ⟨H₂ w, l₂ w⟩ := ⟨fun w => (Λ₂ w).H, fun w => (Λ₂ w).lam, rfl⟩
  have hH' : H₂ = fun w => (Λ₁ w).H := funext fun w => hH w w.2
  subst hH'
  have key : ∀ (p : Pol X.K X.Tau n) (q : Pol L X.Tau n), HEq (MvPolynomial.map c₂ q) (MvPolynomial.map c₁ p) →
      q = MvPolynomial.map ι p := by
    intro p q h
    apply MvPolynomial.map_injective c₂ c₂.injective
    rw [eq_of_heq h, MvPolynomial.map_map, show c₂.comp ι = c₁ from RingHom.ext hc]
  unfold CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have a1 := key _ _ (hf (Quotient.out c) (Quotient.out c) HEq.rfl)
  have a2 := key _ _ (hg (Quotient.out c) (Quotient.out c) HEq.rfl)
  have b1 := csum_res_symm _ h₁ f c
  have b2 := csum_res_symm _ h₁ g c
  have b3 := csum_res_symm _ h₂ f' c
  have b4 := csum_res_symm _ h₂ g' c
  have a1' : (f'.1 c).1 = MvPolynomial.map ι (f.1 c).1 :=
    (congrArg Subtype.val b3).symm.trans (a1.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b1))
  have a2' : (g'.1 c).1 = MvPolynomial.map ι (g.1 c).1 :=
    (congrArg Subtype.val b4).symm.trans (a2.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b2))
  have hp := (baseChangePairingV_holds X.E X.K L ι hstar X.Tau n X.emb lam 1 (f.1 c) (g.1 c) (f'.1 c) (g'.1 c) a1' a2').2
  exact congrArg₂ (· * ·) rfl hp

theorem glue_inv_H_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (A₂ ⟨w.1, hw⟩).H = (A₁ w).H) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      ((A₂.glue B₂).inv ⟨w.1, hw⟩).H = ((A₁.glue B₁).inv w).H := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).H = ((A₁.glue B₁) w).H
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1]
  exact hA ⟨w.1, h1⟩ h2

set_option maxHeartbeats 1000000 in

theorem csum_refTuple {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂}
    (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl)
    (hpre : B₂.toPre = B₁.toPre) (hp : HEq w₂.px w₁.px) (j₁ j₂ : ℕ) (hj : j₁ = j₂)
    (ι : B₁.LL →+* B₂.LL) (hι : ∀ x, B₂.embLL (ι x) = B₁.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hj
  have hstar : ∀ x, ι (star x) = star (ι x) := by
    intro x
    apply B₂.embLL.injective
    rw [hι, B₂.starLL_cx, hι, B₁.starLL_cx]
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx : w₂.px = w₁.px := eq_of_heq hp
  refine csum_round_bc (baseOfColW w₁).fields ι hstar (baseOfColW w₂).tauLL ?_ ((baseOfColW w₁).wts.lamV j₁) ?_
    (Formalism.L2.Col.mtTyKK w₁.I.Ch w₁.I.sel (mu0F (X := (baseOfColW w₁).fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).inv
    (Formalism.L2.Col.mtTyKK w₂.I.Ch w₂.I.sel (mu0F (X := (baseOfColW w₂).fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₁).inv
    ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι h₁ h₂ f g f' g' hf hg
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · refine (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans (Eq.trans ?_ (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
    rw [hpx]
    rfl
  · exact glue_inv_H_of_empty (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ fun w hw => rfl

set_option maxHeartbeats 1000000 in

theorem csum_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ L _ hL a b => ?_
  exact csum_refTuple w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hp ((j : ℕ) + 1) ((j' : ℕ) + 1) (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
    a b (L a) (L b) (hL a) (hL b)

end GlobalTheory.Mem.R3.DefLatBC
