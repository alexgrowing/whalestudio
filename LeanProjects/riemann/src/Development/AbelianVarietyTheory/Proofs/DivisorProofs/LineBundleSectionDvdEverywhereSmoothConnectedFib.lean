import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DivSpread

theorem dvd_of_specializes {X : Scheme.{0}} {V : Type} [CommRing V] (p : X ⟶ Spec (CommRingCat.of V)) {L : LB X}
    (hL : L.IsLB) (s : LB.Sec L) (a : V) {x y : X} (hyx : y ⤳ x)
    (h : ∀ j, x ∈ L.U j → cst p x a ∣ gs (𝟙 X) x (L.U j) (s.f j)) :
    ∀ j, y ∈ L.U j → cst p y a ∣ gs (𝟙 X) y (L.U j) (s.f j) := by
  intro i hyi
  obtain ⟨k, hxk⟩ : ∃ k, x ∈ L.U k := by
    have : x ∈ (⨆ k, L.U k) := hL.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hyk : y ∈ L.U k := hyx.mem_open (L.U k).isOpen hxk
  have sp : ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      gs (𝟙 X) y U b = (X.presheaf.stalkSpecializes hyx).hom (gs (𝟙 X) x U b) := by
    intro U hx b
    rw [gs_eq _ y U (hyx.mem_open U.isOpen hx), gs_eq _ x U hx]
    exact (congrArg (fun φ => φ.hom ((Scheme.Hom.app (𝟙 X) U).hom b))
      (X.presheaf.germ_stalkSpecializes _ hyx)).symm
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z a := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨t, ht⟩ := h k hxk
  have hk : cst p y a ∣ gs (𝟙 X) y (L.U k) (s.f k) := by
    refine ⟨(X.presheaf.stalkSpecializes hyx).hom t, ?_⟩
    rw [sp _ hxk, ht, map_mul, ← hc, ← hc, ← sp (p ⁻¹ᵁ ⊤) (show p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial)]
  have hm : y ∈ L.U i ⊓ L.U k := ⟨hyi, hyk⟩
  have e := congrArg (gs (𝟙 X) y (L.U i ⊓ L.U k)) (s.compat i k)
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
  rw [e]
  exact Dvd.dvd.mul_left hk _

theorem exists_specializes_not_dvd {X : Scheme.{0}} {U W : X.Opens} (c : Γ(X, W)) (f : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (h : ¬ gs (𝟙 X) x W c ∣ gs (𝟙 X) x U f) :
    ∃ y, y ⤳ x ∧ Order.coheight y ≤ 1 ∧ ¬ gs (𝟙 X) y W c ∣ gs (𝟙 X) y U f := by
  by_contra H
  push_neg at H
  apply h
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U ⊓ W) (x := x) ⟨hxU, hxW⟩
  have hVU : V ≤ U := fun z hz => (hVle hz).1
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let fV : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom f
  let cV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom c
  have hgf : ∀ z (hz : z ∈ V), gs (𝟙 X) z U f = (X.presheaf.germ V z hz).hom fV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVU hz, gs_eq _ z V hz]; rfl
  have hgc : ∀ z (hz : z ∈ V), gs (𝟙 X) z W c = (X.presheaf.germ V z hz).hom cV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVW hz, gs_eq _ z V hz]; rfl
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI hlocx := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← Ideal.mem_span_singleton]
  refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one _ _ fun Q hQ hQ1 => ?_
  let P : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ Q
  let Pt : PrimeSpectrum Γ(X, V) := ⟨P, hPp⟩
  have hyV : hV.fromSpec Pt ∈ V := by
    have : hV.fromSpec Pt ∈ Set.range hV.fromSpec := ⟨Pt, rfl⟩
    rwa [hV.range_fromSpec] at this
  let yV : V := ⟨hV.fromSpec Pt, hyV⟩
  have hPt : hV.primeIdealOf yV = Pt := hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf yV)
  have hsp : yV.1 ⤳ x := by
    have hle : Pt ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      show P ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  letI : Algebra Γ(X, V) (X.presheaf.stalk yV.1) := X.presheaf.algebra_section_stalk yV
  have hlocy := hV.isLocalization_stalk yV
  rw [hPt] at hlocy
  have hdim : Order.coheight yV.1 ≤ 1 := by
    rw [← GlobalTheory.ringKrullDim_stalk_le_one_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk yV.1)]
    have := IsLocalization.height_comap (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl Q
    change (P.height : WithBot ℕ∞) ≤ 1
    rw [show P = Ideal.under Γ(X, V) Q from rfl, this]
    exact_mod_cast hQ1
  obtain ⟨t, ht⟩ := H yV.1 hsp hdim
  rw [hgf _ hyV, hgc _ hyV] at ht
  change algebraMap Γ(X, V) _ fV = algebraMap Γ(X, V) _ cV * t at ht
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl t
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at ht
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) ht
  refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * w), ?_, ?_⟩
  · exact (P.primeCompl.mul_mem m.2 w.2 : (m : Γ(X, V)) * w ∉ P)
  · rw [Ideal.mem_span_singleton, hgf x hxV, hgc x hxV]
    change algebraMap Γ(X, V) _ cV ∣ algebraMap Γ(X, V) _ (m * w) * algebraMap Γ(X, V) _ fV
    refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * a), ?_⟩
    rw [← map_mul, ← map_mul, show (m : Γ(X, V)) * w * fV = m * (fV * w) by ring, hm,
      show (m : Γ(X, V)) * (cV * a) = cV * (m * a) by ring]

theorem eq_of_specializes_of_coheight_le_one {X S : Scheme.{0}} (p : X ⟶ S) [Flat p] {y w : X}
    (hy : Order.coheight y ≤ 1) {P' : S} (hP' : P' ⤳ p y) (hne : P' ≠ p y) (hw : w ⤳ y) (he : p w = p y) :
    w = y := by
  by_contra hne'
  have hlt : y < w := lt_of_le_not_ge (show y ≤ w from hw) (fun h => hne' (hw.antisymm h).eq)
  have hmaxw : IsMax w := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hy w hlt
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p (show P' ⤳ p w from he ▸ hP')
  have h1 : w ≤ z := hz
  have h2 : z = w := (hz.antisymm (hmaxw h1)).eq
  exact hne (hpz.symm.trans (h2 ▸ he))

theorem mem_of_not_isUnit_cst {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (y : X)
    (a : R) (h : ¬ IsUnit (cst p y a)) : a ∈ (p y).asIdeal := by
  by_contra ha
  apply h
  have hy : y ∈ p ⁻¹ᵁ ⊤ := show p y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial
  rw [cst, gs_eq p y ⊤ hy]
  refine (X.mem_basicOpen _ y hy).1 ?_
  rw [← Scheme.preimage_basicOpen]
  show p y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [basicOpen_eq_of_affine]
  exact ha

theorem specializes_of_mem_fibre {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIrreducible p] {y : X}
    (hmax : ∀ w, w ⤳ y → p w = p y → w = y) {z : X} (hz : p z = p y) : y ⤳ z := by
  obtain ⟨y', hy'⟩ : y ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; exact hz
  have hg : ∀ t, genericPoint (p.fiber (p y)) ⤳ t := fun t => (genericPoint_spec _).specializes trivial
  have hgm : p (p.fiberι (p y) (genericPoint (p.fiber (p y)))) = p y := by
    have : p.fiberι (p y) (genericPoint (p.fiber (p y))) ∈ Set.range (p.fiberι (p y)) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h1 : p.fiberι (p y) (genericPoint (p.fiber (p y))) = y :=
    hmax _ (by have := (hg y').map (p.fiberι (p y)).continuous; rwa [hy'] at this) hgm
  rw [← h1, ← hz']
  exact (hg z').map (p.fiberι (p y)).continuous

end GlobalTheory.DivSpread

open GlobalTheory.DivSpread in
theorem GlobalTheory.DivSpread.dvd_everywhere : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  intro R _ _ _ _ _ X p hsm hgc e he L hL s q hq hcl x j hxj
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hnot
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom q)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z q := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨y, hyx, hy1, hyn⟩ := exists_specializes_not_dvd c (s.f j) hxj trivial (by rw [hc]; exact hnot)
  rw [hc] at hyn
  have hyj : y ∈ L.U j := hyx.mem_open (L.U j).isOpen hxj
  have hqP : q ∈ (p y).asIdeal := mem_of_not_isUnit_cst p y q fun hu =>
    hyn ⟨hu.unit⁻¹ * gs (𝟙 X) y (L.U j) (s.f j), by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]⟩
  let P0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hP0 : P0 ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hP0' : P0 ≠ p y := fun h => hq (by
    have : q ∈ P0.asIdeal := h ▸ hqP
    exact this)
  have hmax : ∀ w, w ⤳ y → p w = p y → w = y := fun w hw hpe =>
    eq_of_specializes_of_coheight_le_one p hy1 hP0 hP0' hw hpe
  have hey : p (e (p y)) = p y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have h1 : y ⤳ e (p y) := specializes_of_mem_fibre p hmax hey
  have h2 : e (p y) ⤳ e (closedPoint R) := (IsLocalRing.specializes_closedPoint (p y)).map e.continuous
  have hcm : p (e (closedPoint R)) = closedPoint R := by
    show (e ≫ p) (closedPoint R) = _
    rw [he]; rfl
  exact hyn (dvd_of_specializes p hL s q (h1.trans h2) (fun k hk => hcl _ hcm k hk) j hyj)
