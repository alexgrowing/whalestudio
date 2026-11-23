import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
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
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Tr

theorem exists_iota_comp {K₁ K₂ : Type} [Field K₁] [Field K₂] (c₁ : K₁ →+* ℂ) (c₂ : K₂ →+* ℂ)
    (h : Set.range c₁ ⊆ Set.range c₂) : ∃ ι : K₁ →+* K₂, ∀ x, c₂ (ι x) = c₁ x := by
  have hle : c₁.range ≤ c₂.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    exact RingHom.mem_range.2 ⟨z, hz⟩
  let e : K₂ ≃+* c₂.range := RingEquiv.ofBijective c₂.rangeRestrict
    ⟨fun a b hab => c₂.injective (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective c₂⟩
  refine ⟨e.symm.toRingHom.comp ((Subring.inclusion hle).comp c₁.rangeRestrict), fun x => ?_⟩
  have h1 : c₂ (e.symm ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩) = c₁ x := by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩)
    exact this
  exact h1

abbrev baseOfColW {B : Base} {f : Fr B.toPre} {T : TwDat B} (_ : ColW B f T) : Base := B

theorem levelFamily_coefficientChange_liftRound (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG)
    (hH : ∀ w, (Λ₂ w).H = (Λ₁ w).H)
    (hl : ∀ w (h₁ : ↥(Λ₁ w).H) (h₂ : ↥(Λ₂ w).H), (h₁ : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = h₂ →
      ι (((Λ₁ w).lam h₁ : X.Kˣ) : X.K) = (((Λ₂ w).lam h₂ : Lˣ) : L))
    (φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG => d.1.N) Λ₁).EqFun) :
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG => d.1.N) Λ₂).EqFun,
      ∀ d, (φ₂.1 d).1 = MvPolynomial.map ι (φ₁.1 d).1 := by
  refine ⟨⟨fun d => Formalism.L2.Col.hfsJ ι lam (φ₁.1 d), ?_⟩, fun d => rfl⟩
  intro g d
  have hg : g.2.1 ∈ Λ₁.grp := by
    intro w _
    have h' : (g.2.1 w) ∈ (Λ₂ w).H := g.2.2 w (Set.mem_univ _)
    rw [hH w] at h'
    exact h'
  have h1 : φ₁.1 (g • d) = (((Λ₁.chr ⟨g.2.1, hg⟩ : X.Kˣ)) : X.K) •
      Formalism.L2.DIV.rhoVr X.emb lam (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d) := φ₁.2 (g.1, ⟨g.2.1, hg⟩) d
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  show Formalism.L2.Col.hfsJ ι lam (φ₁.1 (g • d)) = (((Λ₂.chr g.2 : Lˣ)) : L) •
    Formalism.L2.DIV.rhoVr (fun τ => ι.comp (X.emb τ)) lam (Formalism.L2.Col.ufGL X.E n g.1) (Formalism.L2.Col.hfsJ ι lam (φ₁.1 d))
  have h2 := Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d)
  erw [h2, h1, Formalism.L2.Col.hfsJ_smul]
  congr 1
  rw [Formalism.L2.Col.LevFam.chr_apply, show Λ₂.chr g.2 = _ from Formalism.L2.Col.piChar_apply _ _ g.2, Units.coe_prod, Units.coe_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ => hl w _ _ rfl

theorem liftRound_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    Formalism.L2.Col.DecoSet X.E n ∅ SG₂ = Formalism.L2.Col.DecoSet X.E n ∅ SG₁ ∧
    ∀ φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).EqFun,
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₂ => d.1.N) Λ₂).EqFun,
      ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (φ₂.1 d₂).1) (MvPolynomial.map c₁ (φ₁.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  refine ⟨rfl, fun φ₁ => ?_⟩
  obtain ⟨φ₂, h⟩ := levelFamily_coefficientChange_liftRound X ι e he lam Λ₁ (Λ₁.coefMap ι) (fun w => rfl) (fun w h₁ h₂ hh => by
    have : h₁ = h₂ := Subtype.ext hh
    subst this
    rfl) φ₁
  refine ⟨φ₂, fun d₁ d₂ hd => ?_⟩
  cases hd
  rw [h, MvPolynomial.map_map]
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  rw [hc']

theorem twistRamifiedPrimes_empty_colTuples {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.QE w.I.sel ((mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
  have e : Formalism.L2.Col.QE w.I.sel (w.I.tup w.I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty w.I
  rw [w.I.trueColumn_tuple_trivial_eq_one] at e
  exact e

theorem rowLevelPrimes_colTuples_eq_vGs {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ _ = _
  rw [twistRamifiedPrimes_empty_colTuples w W]
  ext x
  simp

theorem glue_inv_coefMap_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), A₂ ⟨w.1, hw⟩ = (A₁ w).coefMap ι) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      (A₂.glue B₂).inv ⟨w.1, hw⟩ = ((A₁.glue B₁).inv w).coefMap ι := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).inv = (((A₁.glue B₁) w).inv).coefMap ι
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1, ← Formalism.L2.Col.Lev.coefMap_inv,
    hA ⟨w.1, h1⟩ h2]

theorem levKV_coefMap_of {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {m : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Kˣ) (χ₂ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Lˣ)
    (h : ∀ s c, ((χ₂ s c : Lˣ) : L) = ι ((χ₁ s c : Kˣ) : K)) (nV r t s : ℕ) :
    (⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₂ s) nV r t⟩ :
        Formalism.L2.Col.Lev (𝓞 E ⧸ w.asIdeal) L nV) =
      Formalism.L2.Col.Lev.coefMap ι ⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₁ s) nV r t⟩ := by
  have hχ : χ₂ = fun s => (Units.map ι.toMonoidHom).comp (χ₁ s) :=
    funext fun s => MonoidHom.ext fun c => Units.ext (h s c)
  subst hχ
  have h' : (fun _ : ℕ => (Formalism.L2.Col.extChi (fun s => (Units.map ι.toMonoidHom).comp (χ₁ s)) s)⁻¹) =
      fun _ : ℕ => (Units.map ι.toMonoidHom).comp (Formalism.L2.Col.extChi χ₁ s)⁻¹ :=
    funext fun _ => (congrArg (·⁻¹) (Formalism.L2.Col.extChi_coefMap ι χ₁ s)).trans (Formalism.L2.Col.coefMap_comp_inv ι _)
  exact congrArg (Formalism.L2.Col.Lev.mk (Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t))
    ((congrArg (fun χ => Formalism.L2.Col.lamK χ nV r [t]) h').trans (Formalism.L2.Col.lamK_coefMap ι _ _ _))

theorem lift_refTuple_enl : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ W₁ W₂ hE hv hchi j₁ j₂ hj
  subst hj
  obtain ⟨hpre, -, -, hrange⟩ := hE
  obtain ⟨ι, hι⟩ := exists_iota_comp B₁.embLL B₂.embLL hrange
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  refine liftRound_reidx (baseOfColW w₁).fields ι (baseOfColW w₂).tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · exact (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans ((eq_of_heq hv).trans (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ ?_
    intro w hw
    refine levKV_coefMap_of ι w.1 (fun s => w₁.I.Ch.chi s w) (fun s => w₂.I.Ch.chi s ⟨w.1, hw⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w₂).embLL.injective
    rw [hι]
    exact hchi s s rfl w ⟨w.1, hw⟩ HEq.rfl c c HEq.rfl

end GlobalTheory.Mem.R3.Tr
