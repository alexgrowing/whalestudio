import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimpleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.EpsUnique

theorem index_eq_finrank : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v), IsLocalExt L h → ∀ H : Subgroup (Weil h), (∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) → H.index = Module.finrank K L := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v h hL H hH
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  let f : Weil h → (L →ₐ[K] Ω) := fun σ => (σ : G K Ω).toAlgHom.comp (IsScalarTower.toAlgHom K L Ω)
  have hf : ∀ σ τ : Weil h, f σ = f τ ↔ σ⁻¹ * τ ∈ H := fun σ τ => by
    rw [hH, AlgHom.ext_iff]
    refine forall_congr' fun x => ?_
    show (σ : G K Ω) (algebraMap L Ω x) = (τ : G K Ω) (algebraMap L Ω x) ↔
      (σ : G K Ω).symm ((τ : G K Ω) (algebraMap L Ω x)) = _
    rw [AlgEquiv.symm_apply_eq, eq_comm]
  have hs : Function.Surjective f := fun s => by
    obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
    exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (s.liftNormal_commutes Ω x)⟩
  let g : Weil h ⧸ H → (L →ₐ[K] Ω) := Quotient.lift f fun σ τ hστ => (hf σ τ).2 (QuotientGroup.leftRel_apply.1 hστ)
  have hg : Function.Bijective g := by
    refine ⟨fun a b => Quotient.inductionOn₂ a b fun σ τ e => QuotientGroup.eq.2 ((hf σ τ).1 e), fun s => ?_⟩
    obtain ⟨σ, rfl⟩ := hs s
    exact ⟨QuotientGroup.mk σ, rfl⟩
  rw [Subgroup.index, Nat.card_eq_of_bijective g hg, Nat.card_eq_fintype_card, AlgHom.card]

theorem induces_of_eigenvector : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (r : Weil h' →* Weil h), (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) → (∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r)) → ∀ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (u : Fin n → ℂ) (ξ : Weil h' →* ℂˣ), n = Module.finrank K L → (∀ σ, b.ρ (r σ) u = (ξ σ : ℂ) • u) → Submodule.span ℂ (Set.range fun σ => b.ρ σ u) = ⊤ → ∃ hξ : GlobalTheory.WeilDeligne.IsSmooth ξ, Induces (WD.lpOfChar h' ξ hξ) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' r hr hs n b u ξ hn hu hsp
  have hu0 : u ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin n) := ⟨⟨0, hn ▸ Module.finrank_pos⟩⟩
    refine bot_ne_top (α := Submodule ℂ (Fin n → ℂ)) (hsp ▸ (Submodule.span_eq_bot.2 ?_).symm)
    rintro _ ⟨σ, rfl⟩
    simp
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := (hs _ b.ρ b.smooth).of_le fun σ hσ => by
    have h1 := hu σ
    rw [show b.ρ (r σ) = 1 from hσ] at h1
    exact Units.ext (smul_left_injective ℂ hu0 (by simpa using h1.symm))
  refine ⟨hξ, 1, n, _, b, (LinearMap.proj (0 : Fin 1)).smulRight u, rfl, rfl, by simp [hn], fun σ' σ hσ x => ?_, ?_⟩
  · rw [show σ = r σ' from Subtype.ext (AlgEquiv.ext fun z => (hσ z).trans (hr σ' z).symm)]
    simp [hu, smul_smul, mul_comm]
  · rw [eq_top_iff, ← hsp]
    refine Submodule.span_mono ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨(σ, fun _ => 1), by simp⟩

section One

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem induces_of_charPol {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) : Induces x y := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  obtain ⟨n, b, rfl⟩ := y.exists_rep
  simp only [WD.charPol_mk] at hxy
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq a.ρ b.ρ (GlobalTheory.T.weil_deligne_semisimple E Ω A w h m a) (GlobalTheory.T.weil_deligne_semisimple E Ω A w h n b)
    fun g => by
      have h1 := hxy g
      rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin m)),
        ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n))] at h1
      rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)),
        LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), Matrix.trace_eq_neg_charpoly_nextCoeff,
        Matrix.trace_eq_neg_charpoly_nextCoeff, h1]
  have hmn : n = m := by simpa using e.finrank_eq.symm
  refine ⟨m, n, a, b, e, rfl, rfl, by simp [hmn], fun σ' σ hσ u => ?_, ?_⟩
  · rw [show σ = σ' from Subtype.ext (AlgEquiv.ext hσ)]; exact he _ _
  · exact eq_top_iff.2 fun u _ => Submodule.subset_span ⟨(1, e.symm u), by simp⟩

theorem eps_eq_of_charPol {ε : EpsFamily A} (hε : IsDeligneEps ε) {ψ : AddChar (w.adicCompletion E) Circle}
    (hc : Continuous ψ) (h1 : ψ ≠ 1) {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) :
    ε E w h ψ x = ε E w h ψ y := by
  have := hε.ind E E w w h h (isLocalExt_self h) ψ ψ hc h1 hc (fun z => by simp) x x y x
    (induces_of_charPol hxy) (induces_self x) rfl
  exact (mul_right_cancel this).symm

theorem exists_place (h : IsPlaceOver A w) (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra E L]
    [IsScalarTower E L Ω] : ∃ v : HeightOneSpectrum (𝓞 L), IsPlaceOver A v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := fun x => by
    have h1 : IsIntegral ℤ (algebraMap L Ω x) := x.2.map (algebraMap L Ω).toIntAlgHom
    have h2 : IsIntegral A (algebraMap L Ω x) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hy ▸ y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  have hf : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω x) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h0 => ?_⟩, hf⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have h3 := (hf (algebraMap (𝓞 E) (𝓞 L) x)).1 (by
    have := (h x).2 hx
    rwa [IsScalarTower.algebraMap_apply E L Ω] at this)
  rw [h0, Ideal.mem_bot] at h3
  exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L) (by simpa using h3))

theorem exists_addChar (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L]
    [IsScalarTower E L Ω] {v : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hL : IsLocalExt L h)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ ψL : AddChar (v.adicCompletion L) Circle, Continuous ψL ∧ ψL ≠ 1 ∧
      ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.T.local_trace_completion E L Ω A w v h hv hL
  refine ⟨ψ.compAddMonoidHom T, hc.comp hT, fun h0 => h1 ?_, fun z => by simp [hT']⟩
  ext x
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => (ψ x : ℂ) = (1 : AddChar _ Circle) x) x
    (isClosed_eq (continuous_subtype_val.comp hc) (by simpa using continuous_const)) fun a => ?_
  obtain ⟨z, rfl⟩ := Algebra.trace_surjective E L a
  have := DFunLike.congr_fun h0 (algebraMap L _ z)
  simp only [AddChar.compAddMonoidHom_apply, hT', AddChar.one_apply] at this
  simp [this]

end One

section Two

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem addChar_transport (hP : PlaceIso A w A' w' φ j i) {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x) :
    Continuous ψ' ∧ ψ' ≠ 1 := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w'.adicCompletion E') := charZero_of_injective_algebraMap (algebraMap E' _).injective
  refine ⟨?_, fun h0 => h1 ?_⟩
  · have : (ψ' : _ → Circle) = ψ ∘ i.symm := funext fun x => by simp [← hψ]
    rw [this]
    exact hc.comp (GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation _ _ i hP.cont).1
  · ext x
    simp [← hψ, h0]

theorem eps_char (hG : GlobalArtinReciprocity) (hC : ChevalleyUnits) (hL : LocalLanglandsExists)
    (hP : PlaceIso A w A' w' φ j i) {ε : EpsFamily A} {ε' : EpsFamily A'} (hε : IsDeligneEps ε)
    (hε' : IsDeligneEps ε') {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x)
    {ξ : Weil h →* ℂˣ} (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) {ξ' : Weil h' →* ℂˣ} (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ')
    (hr : ∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') :
    ε E w h ψ (WD.lpOfChar h ξ hξ) = ε' E' w' h' ψ' (WD.lpOfChar h' ξ' hξ') := by
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨-, a, ha, -⟩ := hL E Ω A w h
  obtain ⟨-, a', ha', -⟩ := hL E' Ω' A' w' h'
  obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
  obtain ⟨χ', hχ', rfl⟩ := ha'.factor ξ' hξ'
  obtain ⟨c, hcr, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w'.adicCompletion E') := charZero_of_injective_algebraMap (algebraMap E' _).injective
  refine Units.ext ((GlobalTheory.T.tate_epsilon_transport _ _ i hP.cont ψ ψ' χ χ' _ hψ (fun x => ?_) (hε.char E w h ψ hc h1 a ha χ hχ)).unique
    (hε'.char E' w' h' ψ' hc' h1' a' ha' χ' hχ'))
  obtain ⟨σ, rfl⟩ := ha.surj x
  have h2 := (hcr σ _).2 rfl
  rw [← GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω' A' w' h' φ j i hP a a' ha ha' σ _ h2]
  exact (hr σ _ h2).symm

theorem valuation_lt_one_iff_map (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

theorem eps_ind (hG : GlobalArtinReciprocity) (hC : ChevalleyUnits) (hLL : LocalLanglandsExists)
    (hP : PlaceIso A w A' w' φ j i) {ε : EpsFamily A} {ε' : EpsFamily A'} (hε : IsDeligneEps ε)
    (hε' : IsDeligneEps ε') {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x)
    (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (H : Subgroup (Weil h)) (hH : H.FiniteIndex) (hHo : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H})
    (χ₁ χ₂ : H →* ℂˣ) {n : ℕ} (b₁ b₂ : WDRep h (Fin n → ℂ)) (b₁' b₂' : WDRep h' (Fin n → ℂ))
    (e₁ : ∀ σ, b₁'.ρ (c σ) = b₁.ρ σ) (e₂ : ∀ σ, b₂'.ρ (c σ) = b₂.ρ σ) (v₁ v₂ : Fin n → ℂ) (hn : n = H.index)
    (k₁ : ∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) (k₂ : ∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂)
    (s₁ : Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤)
    (s₂ : Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤) :
    ε E w h ψ (WD.mk b₁) * ε' E' w' h' ψ' (WD.mk b₂') = ε E w h ψ (WD.mk b₂) * ε' E' w' h' ψ' (WD.mk b₁') := by
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨L, hfin, hL, hHL⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hH hHo
  obtain ⟨L', jL, hfin', hL', hdeg, hφ, hadj⟩ :=
    GlobalTheory.T.weil_group_transport E Ω A w h E' Ω' A' w' h' φ j c hP.ext (fun σ => (hcr σ _).2 rfl) L hfin hL
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : NumberField L' := NumberField.of_module_finite E' L'
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsAlgClosure L' Ω' := ⟨IsAlgClosure.isAlgClosed E', Algebra.IsAlgebraic.tower_top (K := E') L'⟩
  obtain ⟨v, hv⟩ := exists_place h L
  obtain ⟨v', hv'⟩ := exists_place h' L'
  have hj : ∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x) := fun x =>
    Subtype.ext ((hφ _).symm.trans (hP.ext x))
  obtain ⟨iL, hiL, hiL'⟩ := GlobalTheory.T.completion_base_change_places E L E' L' w v w' v' j jL i
    (fun x => by rw [← hv, ← h]; rfl) (fun x => by rw [← hv', ← h']; rfl)
    (fun x => by
      rw [← hv, ← hv', ← valuation_lt_one_iff_map hP.mem]
      exact Iff.of_eq (congrArg (fun z => A'.valuation z < 1) (hφ _).symm))
    hj hadj hP.cont hP.loc
  have hPL : PlaceIso A v A' v' φ jL iL := ⟨hP.mem, hφ, hiL, hiL'⟩
  obtain ⟨ψL, hcL, h1L, hψL⟩ := exists_addChar L hv hL hc h1
  obtain ⟨ψL', hcL', -, hψL'⟩ := exists_addChar L' hv' hL' hc' h1'
  have hψi : ∀ x, ψL' (iL x) = ψL x := fun x => by
    refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => ψL' (iL x) = ψL x) x
      (isClosed_eq (hcL'.comp hiL) hcL) fun z => ?_
    rw [hiL', hψL', hψL, GlobalTheory.T.trace_base_change_field E L E' L' j jL hj hadj hdeg, ← hP.loc, hψ]
  obtain ⟨r, hr, hrs⟩ := GlobalTheory.T.weil_group_restriction E L Ω A w v h hv
  obtain ⟨r', hr', hrs'⟩ := GlobalTheory.T.weil_group_restriction E' L' Ω' A' w' v' h' hv'
  have hn' : n = Module.finrank E L := hn.trans (index_eq_finrank E L Ω A w h hL H hHL)
  have m : ∀ σ, r σ ∈ H := fun σ => (hHL _).2 fun x => by rw [hr]; exact (σ : G L Ω).commutes x
  have m' : ∀ σ, (c.symm.toMonoidHom.comp r') σ ∈ H := fun σ => (hHL _).2 fun x => by
    apply φ.injective
    show φ ((c.symm (r' σ) : G E Ω) x) = _
    rw [(hcr _ (r' σ)).2 (c.apply_symm_apply _), hr', hφ]
    exact (σ : G L' Ω').commutes (jL x)
  have key : ∀ (χ : H →* ℂˣ) (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)) (u : Fin n → ℂ),
      (∀ σ, b'.ρ (c σ) = b.ρ σ) → (∀ σ : H, b.ρ σ u = (χ σ : ℂ) • u) →
      Submodule.span ℂ (Set.range fun σ => b.ρ σ u) = ⊤ →
      ∃ (x : WD hv) (x' : WD hv'), Induces x (WD.mk b) ∧ Induces x' (WD.mk b') ∧ x.lpDim = 1 ∧ x'.lpDim = 1 ∧
        ε L v hv ψL x = ε' L' v' hv' ψL' x' := by
    intro χ b b' u e k s
    obtain ⟨p, hp⟩ := induces_of_eigenvector E L Ω A w v h hv r hr hrs n b u (χ.comp (r.codRestrict H m)) hn'
      (fun σ => k ⟨r σ, m σ⟩) s
    obtain ⟨p', hp'⟩ := induces_of_eigenvector E' L' Ω' A' w' v' h' hv' r' hr' hrs' n b' u
      (χ.comp ((c.symm.toMonoidHom.comp r').codRestrict H m')) (hn'.trans hdeg.symm)
      (fun σ => by
        have := k ⟨_, m' σ⟩
        rw [← e] at this
        simpa using this)
      (by
        rw [← s, ← c.surjective.range_comp]
        simp only [Function.comp_def, e])
    refine ⟨_, _, hp, hp', by simp [WD.lpOfChar], by simp [WD.lpOfChar],
      eps_char hG hC hLL hPL hε hε' hcL h1L hψi p p' fun σ σ' hσ => congrArg χ (Subtype.ext ?_)⟩
    show r σ = c.symm (r' σ')
    rw [eq_comm, MulEquiv.symm_apply_eq, eq_comm, ← hcr]
    intro z
    rw [hr, hr']
    exact hσ z
  obtain ⟨x₁, x₁', i₁, i₁', d₁, d₁', q₁⟩ := key χ₁ b₁ b₁' v₁ e₁ k₁ s₁
  obtain ⟨x₂, x₂', i₂, i₂', d₂, d₂', q₂⟩ := key χ₂ b₂ b₂' v₂ e₂ k₂ s₂
  have t := hε.ind E L w v h hv hL ψ ψL hc h1 hcL hψL x₁ x₂ _ _ i₁ i₂ (d₁.trans d₂.symm)
  have t' := hε'.ind E' L' w' v' h' hv' hL' ψ' ψL' hc' h1' hcL' hψL' x₁' x₂' _ _ i₁' i₂' (d₁'.trans d₂'.symm)
  rw [← q₁, ← q₂] at t'
  apply mul_right_cancel (b := ε L v hv ψL x₂)
  rw [mul_right_comm, t, mul_assoc _ (ε' E' w' h' ψ' (WD.mk b₁')), t']
  simp only [mul_assoc, mul_comm, mul_left_comm]

end Two

theorem eps_eq_of_placeIso : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (ε : EpsFamily A) (ε' : EpsFamily A'), IsDeligneEps ε → IsDeligneEps ε' → ∀ (ψ : AddChar (w.adicCompletion E) Circle) (ψ' : AddChar (w'.adicCompletion E') Circle), Continuous ψ → ψ ≠ 1 → (∀ x, ψ' (i x) = ψ x) → ∀ (y : WD h) (y' : WD h'), WDRel φ y y' → ε E w h ψ y = ε' E' w' h' ψ' y' := by
  intro hG hC hB hLL E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP ε ε' hε hε' ψ ψ' hc h1 hψ y y' hy
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨S, hS, -, -, hSadd, -, -, -, -, hSchar⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i hP
  obtain ⟨c, hcr, hdeg, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  have rep : ∀ (n : ℕ) (b : WDRep h (Fin n → ℂ)), ∃ b' : WDRep h' (Fin n → ℂ),
      S (WD.mk b) = WD.mk b' ∧ ∀ σ, b'.ρ (c σ) = b.ρ σ := by
    intro n b
    let b' : WDRep h' (Fin n → ℂ) :=
      { ρ := b.ρ.comp c.symm.toMonoidHom
        N := b.N
        smooth := (hsm _ _).2 (b.smooth.of_le fun σ hσ => by simpa using hσ)
        semisimple := fun σ => b.semisimple _
        nilpotent := b.nilpotent
        comm := fun σ => by
          have := b.comm (c.symm σ)
          rw [← hdeg, c.apply_symm_apply, ← hq] at this
          exact this }
    have hb : ∀ σ, b'.ρ (c σ) = b.ρ σ := fun σ => congrArg b.ρ (c.symm_apply_apply σ)
    exact ⟨b', (hS _ _).1 ⟨n, b, b', rfl, rfl, rfl, fun σ σ' hσ => by rw [← (hcr _ _).1 hσ, hb]⟩, hb⟩
  have hpol : ∀ x σ, (S x).charPol (c σ) = x.charPol σ := by
    intro x σ
    obtain ⟨n, b, rfl⟩ := x.exists_rep
    obtain ⟨b', h2, h3⟩ := rep n b
    rw [h2, WD.charPol_mk, WD.charPol_mk, h3]
  rw [← (hS y y').1 hy]
  refine GlobalTheory.T.epsilon_unique_of_inductive hB E Ω A w h (ε E w h ψ) (fun x => ε' E' w' h' ψ' (S x)) (hε.add E w h ψ hc h1)
    (fun x z => by rw [hSadd, hε'.add E' w' h' ψ' hc' h1']) (fun x z hxz => ⟨eps_eq_of_charPol hε hc h1 hxz,
      eps_eq_of_charPol hε' hc' h1' fun σ => ?_⟩) (fun ξ hξ => ?_)
    (fun H hH hHo χ₁ χ₂ n b₁ b₂ v₁ v₂ hn k₁ k₂ s₁ s₂ => ?_) y
  · obtain ⟨σ, rfl⟩ := c.surjective σ
    rw [hpol, hpol, hxz]
  · have hξ' : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp c.symm.toMonoidHom) :=
      (hsm _ _).2 (hξ.of_le fun σ hσ => by simpa using hσ)
    have hr : ∀ σ σ', WeilRel φ σ σ' → ξ σ = (ξ.comp c.symm.toMonoidHom) σ' := fun σ σ' hσ => by
      simp [← (hcr _ _).1 hσ]
    rw [hSchar ξ hξ _ hξ' hr]
    exact eps_char hG hC hLL hP hε hε' hc h1 hψ hξ hξ' hr
  · obtain ⟨b₁', f₁, e₁⟩ := rep n b₁
    obtain ⟨b₂', f₂, e₂⟩ := rep n b₂
    rw [f₁, f₂]
    exact eps_ind hG hC hLL hP hε hε' hc h1 hψ c hcr H hH hHo χ₁ χ₂ b₁ b₂ b₁' b₂' e₁ e₂ v₁ v₂ hn k₁ k₂ s₁ s₂

end GlobalTheory.LocLanglands.EpsUnique

end
