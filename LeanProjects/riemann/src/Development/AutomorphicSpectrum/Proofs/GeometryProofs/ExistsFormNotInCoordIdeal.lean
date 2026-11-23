import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr

section Alg

open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_form (c : ∀ k, J k) (g : MRing J) :
    ∃ (m : K → ℕ) (G : MRing J), IsMultiHomog G m ∧ ∀ (L : Type) [Field L] (v : (Σ k, J k) → L),
      (∀ k, v ⟨k, c k⟩ ≠ 0) →
        aeval (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩) g * ∏ k, v ⟨k, c k⟩ ^ m k = aeval v G := by
  classical
  induction g using MvPolynomial.induction_on with
  | C n =>
    refine ⟨0, C n, homog_C n, fun L _ v _ => ?_⟩
    simp
  | add a b ha hb =>
    obtain ⟨m, G, hG, ea⟩ := ha
    obtain ⟨n, G', hG', eb⟩ := hb
    refine ⟨m + n, G * cMon c n + G' * cMon c m, homog_add (homog_mul hG (homog_cMon c n)) ?_, fun L _ v hv => ?_⟩
    · rw [add_comm m n]
      exact homog_mul hG' (homog_cMon c m)
    · have hadd : ∏ k, v ⟨k, c k⟩ ^ (m + n) k = (∏ k, v ⟨k, c k⟩ ^ m k) * ∏ k, v ⟨k, c k⟩ ^ n k := by
        simp [pow_add, Finset.prod_mul_distrib]
      rw [hadd, map_add, map_add, map_mul, map_mul, aeval_cMon, aeval_cMon, ← ea L v hv, ← eb L v hv]
      ring
  | mul_X a p ha =>
    obtain ⟨m, G, hG, ea⟩ := ha
    refine ⟨m + Pi.single p.1 1, G * X p, homog_mul hG (homog_X p), fun L _ v hv => ?_⟩
    have h1 : ∏ k, v ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = v ⟨p.1, c p.1⟩ := by
      rw [Fintype.prod_eq_single p.1]
      · simp
      · intro k hk
        simp [Pi.single_apply, hk]
    have hadd : ∏ k, v ⟨k, c k⟩ ^ (m + Pi.single p.1 1 : K → ℕ) k =
        (∏ k, v ⟨k, c k⟩ ^ m k) * v ⟨p.1, c p.1⟩ := by
      rw [← h1]
      simp [pow_add, Finset.prod_mul_distrib]
    rw [hadd, map_mul, map_mul, aeval_X, aeval_X, ← ea L v hv]
    field_simp [hv p.1]

theorem evC_eq_aeval (w : (Σ k, J k) → ℂ) (f : MRing J) : evC w f = aeval w f := by
  simp [evC, MvPolynomial.aeval_def, MvPolynomial.eval_map, MvPolynomial.eval₂_eq']

theorem segre_chart {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) = chartRingZ y c := by
  classical
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    have := GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.prod_update_div (β := J) (fun k (b : J k) => y ⟨k, b⟩) c hc k i
    simpa using this

def ratMap {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) : MRing J →ₐ[ℤ] chartRingZ y c :=
  aeval fun p => ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

theorem ratMap_coe {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (g : MRing J) :
    (ratMap y c g : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g := by
  have : (chartRingZ y c).val.comp (ratMap y c) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [ratMap]
  rw [← this]
  rfl

theorem ratMap_surjective {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) :
    Function.Surjective (ratMap y c) := by
  rintro ⟨r, hr⟩
  have h : r ∈ (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) : MRing J →ₐ[ℤ] Ω).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact hr
  obtain ⟨g, rfl⟩ := h
  exact ⟨g, Subtype.ext (ratMap_coe y c g)⟩

theorem exists_chartEval {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (w : (Σ k, J k) → ℂ) (hw : w ∈ mcPts (mCoordIdeal y)) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ e : chartRingZ y c →+* ℂ, ∀ g : MRing J,
      e (ratMap y c g) = aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) g := by
  let φw : MRing J →+* ℂ := (aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) : MRing J →ₐ[ℤ] ℂ).toRingHom
  have hker : RingHom.ker (ratMap y c).toRingHom ≤ RingHom.ker φw := by
    intro g hg
    obtain ⟨m, G, hG, e⟩ := exists_form c g
    have hy0 : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g = 0 := by
      rw [← ratMap_coe]
      have : ratMap y c g = 0 := hg
      simp [this]
    have hG0 : aeval y G = 0 := by rw [← e Ω y hc, hy0, zero_mul]
    have hmem : G ∈ mCoordIdeal y := mem_of_aeval_eq_zero hG hG0
    have hwG : aeval w G = 0 := by
      rw [← evC_eq_aeval]
      exact hw.2 G hmem
    have hprod : ∏ k, w ⟨k, c k⟩ ^ m k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)
    rw [← e ℂ w hwc] at hwG
    exact (mul_eq_zero.1 hwG).resolve_right hprod
  refine ⟨(ratMap y c).toRingHom.liftOfSurjective (ratMap_surjective y c) ⟨φw, hker⟩, fun g => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ g

end Alg

section Sch

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ev (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens} (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (s : Γ(X, U)) : genMap ξ q (X.presheaf.germ U q.1 hq s) = ev ξ U h s :=
  genMap_germ_eq_stalk_closed ξ q U hq h s

theorem exists_ev_eq {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : genPt ξ ∈ U)
    (sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) (ha : ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) :
    ∃ s, ev ξ U h s = a := by
  let I : Ideal Γ(X, U) :=
    { carrier := {s | ∃ r, a * ev ξ U h s = ev ξ U h r}
      add_mem' := by
        rintro s t ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [map_add, map_add, mul_add, hr, hr']⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t s ⟨r, hr⟩
        exact ⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, ← hr]; ring⟩ }
  by_cases hd : I = ⊤
  · obtain ⟨r, hr⟩ : (1 : Γ(X, U)) ∈ I := hd ▸ Submodule.mem_top
    exact ⟨r, by simpa using hr.symm⟩
  · exfalso
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hd
    let y : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
    have hy : hU.fromSpec y ∈ U := by
      have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
      rwa [hU.range_fromSpec] at this
    let q : Cpt ξ := ⟨hU.fromSpec y, sp _ hy⟩
    letI := X.presheaf.algebra_section_stalk (⟨hU.fromSpec y, hy⟩ : U)
    haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
    obtain ⟨t, ht⟩ := ha q hy
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj y.asIdeal.primeCompl t
    refine s.2 (hIP ⟨r, ?_⟩)
    rw [← genMap_germ h q hy, ← genMap_germ h q hy, ← ht, ← map_mul]
    exact congrArg _ e

theorem germ_closedPoint {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem exists_pt {U : X.Opens} (hU : IsAffineOpen U) (ε : Γ(X, U) →+* ℂ) :
    ∃ (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : z (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U), ∀ s,
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = ε s := by
  let z : Spec (CommRingCat.of ℂ) ⟶ X := Spec.map (CommRingCat.ofHom ε) ≫ hU.fromSpec
  have hz : z (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U := by
    have : z (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ Set.range hU.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hU.range_fromSpec] at this
  refine ⟨z, hz, fun s => ?_⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have h2 : z.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z hz).ge =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom ε)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ε)) hU.fromSpec U ⊤ ⊤ hfs (fun _ _ => trivial)
    rw [Scheme.Hom.appTop]
    rw [← Scheme.Hom.appLE_eq_app (f := Spec.map (CommRingCat.ofHom ε)) (U := ⊤)]
    exact this.symm
  have key : X.presheaf.germ U _ hz ≫ Scheme.stalkClosedPointTo z = CommRingCat.ofHom ε := by
    rw [germ_closedPoint z U hz, h2, h1, Category.assoc, Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  exact congrArg (fun f => f.hom s) key

end Sch

section Core

open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem valAt_quot {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens} (hη : genPt ξ ∈ U)
    (sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (z : Spec (CommRingCat.of ℂ) ⟶ X)
    (hz : z (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U) (su sv : Γ(X, U))
    (hv : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0) :
    ValAt ξ z (ev ξ U hη su / ev ξ U hη sv)
      ((Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz su) /
        (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv)) := by
  have hunit : IsUnit (X.presheaf.germ U _ hz sv) :=
    isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hv)
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint (CommRingCat.of ℂ)), sp _ hz⟩
  have h1 : ev ξ U hη sv * genMap ξ q t = 1 := by
    rw [← genMap_germ hη q hz, ← map_mul, ht, map_one]
  have h2 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) *
      (Scheme.stalkClosedPointTo z).hom t = 1 := by
    rw [← map_mul, ht, map_one]
  refine ⟨sp _ hz, X.presheaf.germ U _ hz su * t, ?_, ?_⟩
  · change genMap ξ q _ = _
    rw [map_mul, genMap_germ hη q hz, div_eq_mul_inv, inv_eq_of_mul_eq_one_right h1]
  · rw [map_mul, div_eq_mul_inv, inv_eq_of_mul_eq_one_right h2]

end Core

section Main

theorem ringInt_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) : Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

theorem exists_ext_frac {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringInt_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringInt_injective r) a⟩

theorem exists_lift_genFibre {F : Type} [Field F] [NumberField F] {W : Scheme.{0}}
    (s : W ⟶ Spec (CommRingCat.of (𝓞 F))) (z : Spec (CommRingCat.of ℂ) ⟶ W) :
    ∃ u : Spec (CommRingCat.of ℂ) ⟶ pullback s (spMap (algebraMap (𝓞 F) F)), u ≫ pullback.fst _ _ = z := by
  let r : 𝓞 F →+* ℂ := (Spec.preimage (z ≫ s)).hom
  have hr : z ≫ s = spMap r := by
    simp [r, spMap]
  obtain ⟨r', hr'⟩ := exists_ext_frac r
  refine ⟨pullback.lift z (spMap r') ?_, pullback.lift_fst _ _ _⟩
  rw [hr, ← hr']
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem genPt_dominates {X' X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let p : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  calc f (genPt ξ') = (ξ' ≫ f) p := (Scheme.Hom.comp_apply ξ' f p).symm
    _ = (Spec.map (CommRingCat.ofHom i) ≫ ξ) p := congrArg (fun g => g p) h
    _ = ξ (Spec.map (CommRingCat.ofHom i) p) := Scheme.Hom.comp_apply _ _ _
    _ = genPt ξ := congrArg ξ (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr
