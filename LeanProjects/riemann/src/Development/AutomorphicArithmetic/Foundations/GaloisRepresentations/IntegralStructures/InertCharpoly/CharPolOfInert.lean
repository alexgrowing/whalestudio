import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnlinkedLanglandsDatumGenericStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumNoMonodromyLengthOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportOfLengthOneLanglandsDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwistStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTameOfMemWeilDeligneListSumStatement
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.DepthZeroIntermediateHolds

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Zero.LLC UpperTheory.GalStar UpperTheory.GalS PositivityTheory.Rg.DzCount
open private UpperTheory.Zero.LLC.AbC.dim_one from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv

namespace UpperTheory.Gal.Int.Row

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isTameWD_of_tmW {y : WD h} (k : TmW y) : IsTameWD y := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  have ha : a.Tame := (WD.tame_mk a).1 ((WD.tame_iff_inePol _).2 fun σ hσ => k σ hσ)
  refine ⟨n, a, rfl, fun σ hσ => ha σ fun x hx => ?_⟩
  have e : (σ : G E Ω) x / x - 1 = ((σ : G E Ω) x - x) / x := by field_simp
  have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
  rw [e, map_div₀, div_lt_one₀ h0]
  exact hσ.2 x hx

theorem dim_one_of_dvd {y : WD h} (hy : IsIrrWD y) (k : ∀ s t : Weil h, ∃ m : ℕ, y.charPol ⁅s, t⁆ ∣ (X - 1 : ℂ[X]) ^ m) :
    y.lpDim = 1 := by
  obtain ⟨n, b, rfl, hb⟩ := hy
  have hn : n = 1 := UpperTheory.Zero.LLC.AbC.dim_one b hb fun σ t => by
    obtain ⟨m, hm⟩ := k σ (ineIncl h t)
    rw [WD.charPol_mk] at hm
    exact ⟨m, hm⟩
  rw [WD.lpDim_mk]
  simpa using hn

theorem tor_of_fix {y : WD h} (ht : IsTameWD y) {γ : G E Ω} (hγ : TameGenAt A γ)
    (k : ∀ z : ℂ, (y.charPol (ineIncl h ⟨γ, hγ.1⟩)).IsRoot z → z ^ (normV w - 1) = 1) : Tor y := by
  obtain ⟨n, a, rfl, ha'⟩ := ht
  have ha : a.Tame := fun σ hσ => ha' σ (TameWeilRepresentationIrreducibility.wild_inertia_isWild hσ)
  let u := a.ρ.toHomUnits
  let g : Weil h := ineIncl h ⟨γ, hγ.1⟩
  have hq : 1 ≤ normV w := (one_lt_normV w).le
  have p1 : a.ρ g ^ (normV w - 1) = 1 := pow_eq_one_of_roots (a.semisimple g) fun z hz => k z (by rwa [WD.charPol_mk])
  have p2 : a.ρ (frob h * g * (frob h)⁻¹) = a.ρ g := by
    rw [ha.conj_eq_pow hγ.1 deg_frob, ← Nat.sub_add_cancel hq, pow_succ, p1, one_mul]
  have c1 : Commute (u (frob h)) (u g) := by
    have e : u (frob h * g * (frob h)⁻¹) = u g := Units.ext p2
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at e
    exact e
  have cen : ∀ x : (End ℂ (Fin n → ℂ))ˣ, Commute x (u g) → ∀ σ, Commute x (u (ineIncl h σ)) := fun x hx σ =>
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_of_gen ha hγ (Subgroup.centralizer {x}) (Subgroup.mem_centralizer_singleton_iff.2 hx.symm) σ) |>.symm
  have c2 := cen _ c1
  have c3 : ∀ τ σ, Commute (u (ineIncl h τ)) (u (ineIncl h σ)) := fun τ => cen _ (cen _ (Commute.refl _) τ).symm
  intro s t
  have c : Commute (u s) (u t) := by
    obtain ⟨τ, e⟩ := exists_eq_zpow_mul deg_frob s
    obtain ⟨τ', e'⟩ := exists_eq_zpow_mul deg_frob t
    rw [e, e', map_mul, map_mul, map_zpow, map_zpow]
    exact Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ _ _) ((c2 τ').zpow_left _))
      (Commute.mul_right ((c2 τ).symm.zpow_right _) (c3 τ τ'))
  have e : a.ρ ⁅s, t⁆ = 1 := by
    have := (map_commutatorElement u s t).trans (commutatorElement_eq_one_iff_commute.2 c)
    exact congrArg Units.val this
  show (WD.mk a).charPol _ = _
  rw [WD.charPol_mk, e, LinearMap.charpoly_one, WD.lpDim_mk]

variable {rc : IrrGL (w.adicCompletion E) → WD h}

theorem split (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep) (hm : (rc x).mono0) :
    ∃ l : List (IrrGL (w.adicCompletion E)), HasSupport x.rep (l : Multiset _) ∧ GlobalTheory.RoadU.Unlinked (l : Multiset (IrrGL (w.adicCompletion E))) ∧
      rc x = sumList (l.map rc) := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨c, Δ, hun, hL⟩ := GlobalTheory.T.exists_unlinked_langlandsDatum_generic _ x hx
  obtain ⟨a, ha, L⟩ := id hrc
  have e : rc x = segSum rc (List.ofFn Δ) := L.langlands _ x hL
  obtain ⟨hlen, hsum⟩ := GlobalTheory.T.segmentSum_no_monodromy_length_one rc hrc (List.ofFn Δ) (e ▸ hm)
  have h1 : ∀ i, (Δ i).len = 1 := fun i => hlen _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  refine ⟨List.ofFn fun i => (Δ i).first, ?_, ?_, ?_⟩
  · rw [← Fin.univ_val_map]; exact GlobalTheory.T.supercuspidalSupport_of_lengthOne_langlandsDatum _ c Δ x h1 hL
  · rw [← Fin.univ_val_map]; exact GlobalTheory.T.unlinkedLengthOneSegments_firstTerms_not_nuTwist rc hrc c Δ h1 hun
  · rw [e, hsum, List.map_ofFn, List.map_ofFn]; rfl

theorem plainTor_of_tor (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep) (ht : Tor (rc x))
    (hm : (rc x).mono0) : GlobalTheory.RoadU.PlainTor x := by
  obtain ⟨l, hs, hu, e⟩ := split hrc hx hm
  obtain ⟨a, ha, L⟩ := hrc
  refine ⟨_, hs, fun y hy => ?_, hu⟩
  rw [← L.dim y]
  refine dim_one_of_dvd (L.cusp y (hs.isCusp hy)) fun s t => ⟨(rc x).lpDim, ?_⟩
  have k : (rc x).charPol ⁅s, t⁆ = _ := ht s t
  rw [← k, e, CuspExt.charPol_sumList, List.map_map]
  exact List.dvd_prod (List.mem_map.2 ⟨y, hy, rfl⟩)

theorem good_of_dz (hq : IsQp w) {y : IrrGL (w.adicCompletion E)} (hy : y.IsCusp) (hd : DZ y) : Good y := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have h1 : IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
    simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
  exact ((goodSeg _).2.1 y hy).2 (Or.inr ⟨hq, y, 1, h1, hd, (y.tw_one h1).symm⟩)

theorem dz_of_cusp (hq : IsQp w) (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) (ht : IsTameWD (rc x)) :
    DZ x := by
  obtain ⟨a, ha, H⟩ := hrc
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) (-1)
  have hord : ord (w.adicCompletion E) (a φ) = 1 := by rw [ha.ord_eq, hφ]; rfl
  have hc : ((rc x).eig φ).prod ≠ 0 := by
    obtain ⟨δ, hδ⟩ := (wDBasic E Ω A w h (rc x)).1
    rw [hδ]
    exact Units.ne_zero _
  obtain ⟨f, hf, hfi⟩ := depth_zero_intermediate_holds E Ω A w h φ hφ x.1 _ hx.1
  obtain ⟨Y, hY, hYi⟩ := depth_zero_count_holds (w.adicCompletion E) x.1 hx.1 (a φ) hord (Units.mk0 _ hc)
  have hg : ∀ P ∈ Lab 𝓀[w.adicCompletion E] x.1, Good (Y P) := fun P hP => good_of_dz hq (hY P hP).2.1 (hY P hP).2.2.1
  have hmap : Set.MapsTo (rc ∘ Y) (Lab 𝓀[w.adicCompletion E] x.1) (TameSet φ x.1 ((rc x).eig φ).prod) := by
    intro P hP
    obtain ⟨h1, h2, h3, ω, h4, h5⟩ := hY P hP
    refine ⟨H.cusp _ h2, H.depth _ (hg P hP) h3, (H.dim _).trans h1, ?_⟩
    show ((rc (Y P)).eig φ).prod = _
    rw [H.central _ ω (hg P hP) h4 φ, h5, Units.val_mk0]
  have hinj : Set.InjOn (f ∘ rc ∘ Y) (Lab 𝓀[w.adicCompletion E] x.1) :=
    hfi.comp (fun P hP P' hP' e => hYi hP hP' (H.inj _ _ (hg P' hP') e)) hmap
  have hbij := ((lab_finite _ _).injOn_iff_bijOn_of_mapsTo (hf.comp hmap)).1 hinj
  have hxT : rc x ∈ TameSet φ x.1 ((rc x).eig φ).prod := ⟨H.cusp _ hx, ht, H.dim _, rfl⟩
  obtain ⟨P, hP, hPe⟩ := hbij.surjOn (hf hxT)
  have e : x = Y P := H.inj _ _ (hg P hP) (hfi (hmap hP) hxT hPe).symm
  rw [e]
  exact (hY P hP).2.2.1

theorem charPol_of_inert (hrc : IsRecT h rc) {y z : IrrGL (w.adicCompletion E)} (hy : Good y) (k : y.Inert z)
    (t : Ine (F := E) A) : (rc z).charPol (ineIncl h t) = (rc y).charPol (ineIncl h t) := by
  obtain ⟨a, ha, H⟩ := hrc
  obtain ⟨μ, hμ, rfl⟩ := k
  rw [H.twist _ _ _ hy, H.one, lpChar_lpOfChar]
  obtain ⟨n, b, hb⟩ := (rc y).exists_rep
  have h1 : μ (a (ineIncl h t)) = 1 :=
    hμ _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero]))
  rw [← hb, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, MonoidHom.comp_apply, h1, Units.val_one, one_smul]

theorem mixed_of_tame (hq : IsQp w) (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep)
    (ht : TmW (rc x)) (hs : Sqf (rc x)) (hm : (rc x).mono0) :
    DZ x ∧ ∀ s, HasSupport x.rep s → GlobalTheory.RoadU.Unlinked s ∧ (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨l, hl, hu, e⟩ := split hrc hx hm
  have tame : ∀ y ∈ l, IsTameWD (rc y) := fun y hy =>
    GlobalTheory.T.isTame_of_mem_weilDeligneListSum _ (e ▸ isTameWD_of_tmW ht) _ (List.mem_map_of_mem hy)
  have dz : ∀ y ∈ l, DZ y := fun y hy => dz_of_cusp hq hrc (hl.isCusp hy) (tame y hy)
  obtain ⟨hGL, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  refine ⟨GlobalTheory.DepthZeroPass.depthZeroInduction hGL GlobalTheory.bernsteinZelevinskyFiniteness_holds hZ _ x _ hl dz, fun s hs' => ?_⟩
  obtain rfl : s = (l : Multiset _) := (goodSeg _).2.2 x _ _ hs' hl
  refine ⟨hu, _, Multiset.filter_coe _ l, ?_⟩
  rw [List.pairwise_filter, List.pairwise_iff_forall_sublist]
  intro y z hsub h2 _ hI
  have hy : y ∈ l := hsub.subset (by simp)
  obtain ⟨γ, hγ⟩ : ∃ γ : G E Ω, TameGenAt A γ := GlobalTheory.exists_tameGenAt_of_isPlaceOver E Ω A w h
  have e1 := charPol_of_inert hrc (good_of_dz hq (hl.isCusp hy) (dz y hy)) hI ⟨γ, hγ.1⟩
  have hd : (rc y).charPol (ineIncl h ⟨γ, hγ.1⟩) * (rc y).charPol (ineIncl h ⟨γ, hγ.1⟩) ∣ (rc x).charPol (ineIncl h ⟨γ, hγ.1⟩) := by
    rw [e, CuspExt.charPol_sumList, List.map_map]
    have := (hsub.map ((fun v : WD h => v.charPol (ineIncl h ⟨γ, hγ.1⟩)) ∘ rc)).prod_dvd_prod
    simpa [e1] using this
  have T : Tor (rc y) := tor_of_fix (tame y hy) hγ fun c hc => by
    refine hs γ hγ.1 hγ.2 c ?_
    rw [WD.inePol_of_mem_Ine _ hγ.1, le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero, pow_two]
    exact (mul_dvd_mul (dvd_iff_isRoot.2 hc) (dvd_iff_isRoot.2 hc)).trans hd
  obtain ⟨a, ha, H⟩ := hrc
  have d1 := dim_one_of_dvd (H.cusp y (hl.isCusp hy)) fun s t => ⟨_, (T s t : (rc y).charPol ⁅s, t⁆ = _).dvd⟩
  rw [H.dim] at d1
  simp only [decide_eq_true_eq] at h2
  omega

theorem dz_of_nu {x : IrrGL (w.adicCompletion E)} (h0 : 0 < x.1) (s : ℂ) (k : DZ (x.nu s)) : DZ x := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have e : x = (x.nu s).nu (-s) := by simp
  rw [e]
  refine (twTame _ (x.nu s) _ (isSmoothChar_absPow (-s)) h0 k).2 fun u hu => ?_
  have h1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 := by
    have := (valuation (w.adicCompletion E)).map_one_add_of_lt hu
    simpa using this
  exact isUnram_absPow _ _ _ h1

end UpperTheory.Gal.Int.Row
