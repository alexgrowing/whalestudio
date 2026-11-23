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
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

open Formalism.L2.Col in

theorem repCSD_lift_of_reading {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
    (S : GSD K) (S' : GSD K') (hS : S.Ok) (hS' : S'.Ok) {A A' : Type} [Group A] [Group A']
    (ρ : Representation K A S.EqFun) (ρ' : Representation K' A' S'.EqFun) {T T' : Type} (rd : S.V → T) (rd' : S'.V → T')
    (hrd' : Function.Injective rd') (L : (S.toCSD hS).Forms → (S'.toCSD hS').Forms)
    (hC : ∀ (f : (S.toCSD hS).Forms) (d : S.D) (d' : S'.D), HEq d' d →
      HEq (rd' ((((S'.res hS').symm (L f) : S'.EqFun) : S'.D → S'.V) d')) (rd ((((S.res hS).symm f : S.EqFun) : S.D → S.V) d)))
    (hex : ∀ d' : S'.D, ∃ d : S.D, HEq d' d) (a : A) (a' : A') (t : S.D → S.D) (t' : S'.D → S'.D)
    (hρ : ∀ (φ : S.EqFun) d, (ρ a φ : S.D → S.V) d = (φ : S.D → S.V) (t d))
    (hρ' : ∀ (φ : S'.EqFun) d, (ρ' a' φ : S'.D → S'.V) d = (φ : S'.D → S'.V) (t' d))
    (ht : ∀ (d : S.D) (d' : S'.D), HEq d' d → HEq (t' d') (t d)) (f : (S.toCSD hS).Forms) :
    S'.repCSD hS' ρ' a' (L f) = L (S.repCSD hS ρ a f) := by
  apply (S'.res hS').symm.injective
  apply Subtype.ext
  funext d'
  apply hrd'
  obtain ⟨d, hd⟩ := hex d'
  have e1 : (S'.res hS').symm (S'.repCSD hS' ρ' a' (L f)) = ρ' a' ((S'.res hS').symm (L f)) := by
    simp [GSD.repCSD]
  have e2 : (S.res hS).symm (S.repCSD hS ρ a f) = ρ a ((S.res hS).symm f) := by
    simp [GSD.repCSD]
  rw [e1, hρ']
  have h1 := hC f (t d) (t' d') (ht d d' hd)
  have h2 := hC (S.repCSD hS ρ a f) d d' hd
  rw [e2, hρ] at h2
  exact eq_of_heq (h1.trans h2.symm)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC

open Formalism.L2.Col in

theorem decoratedLattice_translates_heq_of_eq_primes {X : Fields} {n r : ℕ} (h : r ≤ n) {SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : Q' = Q) :
    (∀ d' : DecoSet X.E n ∅ (uSG SG Q'), ∃ d : DecoSet X.E n ∅ (uSG SG Q), HEq d' d) ∧
    ∀ (g : G0 X.E SG r) (d : DecoSet X.E n ∅ (uSG SG Q)) (d' : DecoSet X.E n ∅ (uSG SG Q')), HEq d' d →
      HEq (((1 : UF X.E n), (extGLG Q' (diagonalEmbeddingProduct SG h g))⁻¹) • d') (((1 : UF X.E n), (extGLG Q (diagonalEmbeddingProduct SG h g))⁻¹) • d) := by
  subst hQ
  exact ⟨fun d' => ⟨d', HEq.rfl⟩, fun g d d' hd => by cases hd; rfl⟩

open Formalism.L2.Col in

theorem decoratedLattice_translates_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E))
    (sel' : HeightOneSpectrum (𝓞 B'.fields.F) → HeightOneSpectrum (𝓞 B'.fields.E)) {S S' : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K S) (mu' : Tup B'.fields.F B'.fields.E B'.fields.K S')
    (hQ : QE sel (mu : Chr B.fields.F B.fields.E B.fields.K) = ∅)
    (hQ' : QE sel' (mu' : Chr B'.fields.F B'.fields.E B'.fields.K) = ∅) :
    (∀ d' : DecoSet B'.fields.E B'.R.nV ∅ (rowSG (B'.primes px') sel' mu'),
      ∃ d : DecoSet B.fields.E B.R.nV ∅ (rowSG (B.primes px) sel mu), HEq d' d) ∧
    ∀ (g : Gc B px) (g' : Gc B' px'), HEq g' g → ∀ (d : DecoSet B.fields.E B.R.nV ∅ (rowSG (B.primes px) sel mu))
      (d' : DecoSet B'.fields.E B'.R.nV ∅ (rowSG (B'.primes px') sel' mu')), HEq d' d →
      HEq (((1 : UF B'.fields.E B'.R.nV), (unipotentGroupBlockEmbedding (B'.primes px') sel' mu' (r_le_nV B'.R) g')⁻¹) • d')
        (((1 : UF B.fields.E B.R.nV), (unipotentGroupBlockEmbedding (B.primes px) sel mu (r_le_nV B.R) g)⁻¹) • d) := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  refine ⟨fun d' => (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).1 d', fun g g' hg d d' hd => ?_⟩
  have e := eq_of_heq hg
  subst e
  exact (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).2 _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC
set_option maxHeartbeats 8000000 in

theorem GlobalTheory.Mem.R3.DefLatBC.act_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ _ e he L _ hC g f0 => ?_
  have hP := GlobalTheory.Mem.R3.DefLatBC.decoratedLattice_translates_heq_of_eq_preData B B' w.px w'.px hE.1 hp w.I.sel w'.I.sel
    (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
    (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _) (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _)
  have hinj : Function.Injective fun v : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V => MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) v.1 :=
    (MvPolynomial.map_injective _ (B'.embLL : B'.fields.K →+* ℂ).injective).comp Subtype.val_injective
  exact GlobalTheory.Mem.R3.DefLatBC.repCSD_lift_of_reading (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1))
    (fun v => MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) v.1) _ hinj (fun x => L x) hC hP.1 g (e g) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun d d' hd => hP.2 g (e g) (he g) d d' hd) f0
