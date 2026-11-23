import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RcUnlinkedChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeakRepIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
open UpperTheory.Zero.LLC GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.RoadU UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.UnramifiedSatakeFrobeniusCompatibility

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem charPol_chars {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) {n : ℕ}
    (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hs : HasSupport x.rep (chars ξ hξ))
    (hu : Unlinked (chars ξ hξ)) (g : Weil h) : (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      Pr.zel _ x _ _ hs (GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm)
  have hterm : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩
  have hone : ∀ Δ ∈ 𝔪, Δ.len = 1 := fun Δ hΔ => by
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hterm Δ hΔ ⟨1, h2⟩) _ (hterm Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := fun Δ hΔ => by
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hone Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum]
    congr 1
    refine List.map_congr_left fun Δ hΔ => ?_
    rw [hone Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol : ∀ j, (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := fun j => by
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have hprod : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
    rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol j).symm)
  rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map, hprod, he, hsupp, Multiset.map_map,
    ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  rfl

private theorem satWD_mono0 (n : ℕ) (B : Multiset ℂˣ) : (satWD h n B).mono0 := by
  unfold satWD
  rw [WD.monomial_twist_iff]
  exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))

private theorem satWD_unr (n : ℕ) (B : Multiset ℂˣ) : (satWD h n B).unr := by
  unfold satWD
  rw [WD.unr_tw]
  exact (WD.unr_mk _).2 (WDRep.unr_diag _)

end Local

section Global

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem rec_eq_sat (hn : 1 ≤ n) (π : CuspSub E n) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    {h : IsPlaceOver A w} {σ : SmIrr (GL (Fin n) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) {B : Multiset ℂˣ}
    (hB : (CG.mk π).HasSat w B) {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRecT h rc)
    (hP : PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) (hm : (rc (algNorm σ)).mono0) : rc (algNorm σ) = satWD h n B := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, hL⟩ := hrc
  obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π w B).1 hB) hσ
  have hBσ : GlobalTheory.LFun.HasSatGL w σ.ρ B := hα ▸ GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hS
  obtain ⟨ξ, hξ, ϖ, hsup, hunr, hϖ, rfl⟩ := GlobalTheory.T.supercuspidal_support_characters E n hn w σ B hBσ
  have hun : Unlinked (chars ξ hξ) := by
    obtain ⟨s, hs, -, hu⟩ := hP
    rwa [GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      Pr.zel _ _ _ _ hs hsup] at hu
  set s : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) with hs
  let ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow _ s
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' s
    (fun _ => rfl)
  have h2 := charPol_chars hL (algNorm σ) ξ' hξ' (hnu.1.1 hsup) (hnu.2.1 hun)
  have h3 := GlobalTheory.SatChar.satWD_charPol_chars Ω E w A h n ξ ξ' (fun _ => rfl) hunr ϖ hϖ a ha
  exact GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ hm (satWD_mono0 n _) fun g => (h2 g).trans (h3 g).symm

private theorem frobEig_of {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {B : Multiset ℂˣ}
    (H : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), wdOf h hl ι r = satWD h n B) :
    FrobEig ι r w (algSat n (normV w) B) := by
  intro A h
  have hm : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (Qbar l)) := Units.continuous_val.comp hr
  have hw := H A h
  obtain ⟨t, ht, φ, hφ, N', a, hN, -⟩ := isWDOf_wdOf (h := h) (r := r) hl ι hm
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact satWD_unr n B), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have k := charPol_wdOf (h := h) (r := r) hl ι hm (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, GlobalTheory.SatChar.charPol_satWD, deg_inv, hd] at k
  refine k.symm.trans ?_
  simp only [algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, zpow_neg_one, inv_inv, ← Complex.cpow_neg]
  congr 4
  push_cast
  ring

end Global

section Main

variable {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {n : ℕ}

private theorem plain_all (hn : 1 ≤ n) {π : CuspSub F n} {w : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (hσ : π.IsLocComp w σ)
    (hP : PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) :
    ∀ σ', π.IsLocComp w σ' → PlainTor (IrrGL.of σ'.ρ σ'.smooth σ'.irred) := by
  obtain ⟨s, hs, h1, hu⟩ := hP
  obtain ⟨-, huniq, hT, -, -⟩ := UpperTheory.V.Z.Gam.suppFacts F n hn π w
  have hsa : UpperTheory.V.Z.Gam.SuppAt π w s := ⟨σ, hσ, hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
  intro σ' hσ'
  obtain ⟨s', hs', -⟩ := ((hT s hsa).1.2 h1) σ' hσ'
  obtain rfl : s' = s := huniq s' s ⟨σ', hσ', hs'.of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).symm⟩ hsa
  exact ⟨s', hs', h1, hu⟩

private theorem gd_of (H : PlainRec) (hn : 1 ≤ n) {π : CuspSub F n} {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRecT h rc)
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (hσ : π.IsLocComp w σ)
    (hall : ∀ σ', π.IsLocComp w σ' → PlainTor (IrrGL.of σ'.ρ σ'.smooth σ'.irred)) :
    UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0 := by
  obtain ⟨h1, h2⟩ := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff F n hn π w).1 hall
  obtain ⟨t, ht⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf F n hn π
  exact (H F Ω A w h rc hrc n π t (ht w h1 h2) σ hσ).2

end Main

end UpperTheory.V.Z.Win.UnramifiedSatakeFrobeniusCompatibility

open UpperTheory.V.Z.Win.UnramifiedSatakeFrobeniusCompatibility in
theorem UpperTheory.V.Z.Win.compatTOf :
    UpperTheory.V.Z.Win.CompatTOf := by
  intro hRow H F Ω _ _ _ _ _ _ l _ ι n hn r π hr hreg ⟨χ, hχ⟩ ha
  obtain ⟨R, wt, HT, P⟩ := hRow F Ω l ι n hn π χ hreg hχ
  have hRc : Continuous fun g => (R g : Matrix (Fin n) (Fin n) (Qbar l)) := Units.continuous_val.comp P.cont
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine GlobalTheory.IsoOfFrobFree.main F Ω l ι n R r P.cont hr P.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    refine ⟨_, frobEig_of P.cont hw fun A h => ?_, hf⟩
    obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists F Ω A w h
    obtain ⟨⟨s, σ, hσ, -⟩, -⟩ := UpperTheory.V.Z.Gam.suppFacts F n hn π w
    have hall := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff F n hn π w).2 (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl F n hn π w B hB)
    obtain ⟨g1, g2⟩ := gd_of H hn hrc hσ hall
    rw [(P.away w hw A h rc hrc σ hσ).tor g1 g2]
    exact rec_eq_sat hn π hσ hB hrc (hall σ hσ) g2
  refine ⟨HT, P.weights, fun w σ hσ => ⟨fun A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj hg => ?_⟩, fun hT A h O _ _ _ Bw hj => ?_⟩⟩
  · exact WDT.of_conj ⟨wdOf h hw ι R, isWDOf_wdOf hw ι hRc, fun g => (P.away w hw A h rc hrc σ hσ).tor g.1 g.2⟩ hw p
      fun g => by rw [hp, inv_mul_cancel_right]
  · obtain ⟨-, k2, -, k4⟩ := (P.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice σ hσ rc hrc (Or.inr hg.1) hg.2
    have h3 := GlobalTheory.PstConj.main F Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := F) A).subtype)
      (r.comp (Dec (F := F) A).subtype) p (fun g => hp g.1) k2
    exact ⟨h3.1, by rw [h3.2]; exact k4.tor hg.1 hg.2⟩
  · obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists F Ω A w h
    obtain ⟨g1, g2⟩ := gd_of H hn hrc hσ (plain_all hn hσ hT)
    obtain ⟨k1, -, k3, -⟩ := (P.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice σ hσ rc hrc (Or.inr g1) g2
    obtain ⟨d1, -, -, d4⟩ := GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n (R.comp (Dec (F := F) A).subtype)
      (r.comp (Dec (F := F) A).subtype) p fun g => hp g.1
    exact ⟨d1 k1, fun τ LL' τ' hi => d4 τ _ (k3 τ LL' τ' hi)⟩

end
