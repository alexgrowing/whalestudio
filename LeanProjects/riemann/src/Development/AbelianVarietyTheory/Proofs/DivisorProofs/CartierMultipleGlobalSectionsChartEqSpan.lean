import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCartierMultipleChartIffRegularCodimOneStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ChartSpan

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem gp_comp {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  have h : spMap (GlobalTheory.Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem cst_comp {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp S) (a : R →+* S) :
    GlobalTheory.Desc.cst (p ≫ spMap a) = (GlobalTheory.Desc.cst p).comp a :=
  sp_inj (by rw [← gp_comp, ← sp_comp, ← gp_comp, Category.assoc])

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _

theorem cst_injective {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (e : Sp R ⟶ X)
    (he : e ≫ p = 𝟙 _) : Function.Injective (GlobalTheory.Desc.cst p) := by
  have h1 : Function.Injective p.appTop.hom := by
    have h : p.appTop ≫ e.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    refine Function.LeftInverse.injective (g := e.appTop.hom) fun a => ?_
    exact congrArg (fun g => CommRingCat.Hom.hom g a) h
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  exact (fnOf_injective ⊤ trivial).comp (h1.comp h2)

theorem injective_of_flat {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S] (ρ : R →+* S)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  have := Module.Flat.isSMulRegular_of_isRegular (M := S) (IsRegular.of_ne_zero hne)
  have h2 : (1 : S) = 0 := this (by
    change r • (1 : S) = r • (0 : S)
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact hr)
  exact one_ne_zero h2

theorem coheight_le_one {H S : Scheme.{0}} (p : H ⟶ S) (hp : GeneralizingMap p) (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

theorem height_of_vert {S : Type} [CommRing S] [IsDomain S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] {f : S}
    (hf : f ≠ 0) {z : X} (hz : Vert p f z) : (p z).asIdeal.height = 1 := by
  have h1 := hz.1
  rw [ringKrullDim_stalk_eq_coheight] at h1
  have h2 : Order.coheight z ≤ 1 := le_of_eq (by exact_mod_cast h1)
  have h3 := coheight_le_one p (Flat.generalizingMap p) z h2
  rw [← idealHeight_eq_coheight] at h3
  haveI := (p z).isPrime
  refine le_antisymm h3 (Order.one_le_iff_ne_zero.2 fun h => ?_)
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have := hz.2
  rw [h] at this
  exact hf this

theorem exists_vert_le {S : Type} [CommRing S] [IsDomain S] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] {f : S} (hf : f ≠ 0) (x : X) (hfx : f ∈ (p x).asIdeal) :
    ∃ z : X, Vert p f z ∧ (p z).asIdeal ≤ (p x).asIdeal := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ (g : S) (q : PrimeSpectrum Γ(X, U)), g ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom g ∈ q.asIdeal := by
    intro g q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ (g : S) (y : U), g ∈ (p y.1).asIdeal ↔ φ.hom g ∈ (hU.primeIdealOf y).asIdeal := by
    intro g y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' f ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' f ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ⟨?_, (key' f z).2 (by rw [hP]; exact haQ)⟩, fun g hg => ?_⟩
  · have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [this, hP]
    change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
    rw [hQ1]; rfl
  · have h2 := (key' g z).1 hg
    rw [hP] at h2
    exact (key' g ⟨x, hx⟩).2 (hQx h2)

theorem exists_vert_over {S : Type} [CommRing S] [IsDomain S] [IsNoetherianRing S] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (p : X ⟶ Sp S) (e : Sp S ⟶ X) (he : e ≫ p = 𝟙 _) {f : S} (hf : f ≠ 0)
    (q : Ideal S) [hq : q.IsPrime] (h1 : q.height = 1) (hfq : f ∈ q) : ∃ z : X, Vert p f z ∧ (p z).asIdeal = q := by
  have hpe : ∀ y : Sp S, p (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsDominant p := ⟨Function.Surjective.denseRange fun y => ⟨e y, hpe y⟩⟩
  let y : Sp S := (⟨q, hq⟩ : PrimeSpectrum S)
  obtain ⟨z, hz, hle⟩ := exists_vert_le p hf (e y) (by rw [hpe]; exact hfq)
  rw [hpe] at hle
  refine ⟨z, hz, ?_⟩
  haveI := (p z).isPrime
  refine Ideal.eq_of_le_of_height_le (I := (p z).asIdeal) (J := q) hle ?_
  rw [h1]
  refine Order.one_le_iff_ne_zero.2 fun h => ?_
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have := hz.2
  rw [h] at this
  exact hf this

theorem theta_comp (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (GlobalTheory.Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, h1, h2⟩ := σ.hθ x
  apply sp_inj
  rw [← sp_comp, ← sp_comp, Setup.c₀, ← gp_comp, ← gp_comp, ← reassoc_of% h2, ← h1, (σ.cart x).w]
  simp only [Category.assoc]

theorem isUnit_of_not_mem (σ : Setup) (x : Sp σ.R) {s : σ.R} (hs : s ∉ x.asIdeal) : IsUnit (σ.ρ x s) := by
  have h := (σ.C x).centre
  rw [σ.hρ x] at h
  by_contra hu
  apply hs
  rw [← h]
  exact (mem_maximalIdeal _).2 hu

theorem W_closed (σ : Setup) (x : Sp σ.R) :
    (∀ a ∈ σ.W x, ∀ b ∈ σ.W x, a + b ∈ σ.W x) ∧ (∀ r, ∀ a ∈ σ.W x, σ.c₀ r * a ∈ σ.W x) ∧
      (∀ s, s ∉ x.asIdeal → ∀ a ∈ σ.W x, (σ.c₀ s)⁻¹ * a ∈ σ.W x) := by
  have hc : ∀ r, σ.θ x (σ.c₀ r) = GlobalTheory.Desc.cst (σ.C x).G.hom (σ.ρ x r) := fun r =>
    RingHom.congr_fun (theta_comp σ x) r
  refine ⟨fun a ha b hb z hz => ?_, fun r a ha z hz => ?_, fun s hs a ha z hz => ?_⟩
  · rw [map_add]; exact (ha z hz).add (hb z hz)
  · rw [map_mul, hc]; exact (regAt_cst _ _ _).mul (ha z hz)
  · obtain ⟨u, hu⟩ := isUnit_of_not_mem σ x hs
    rw [map_mul, map_inv₀, hc, ← hu, ← map_units_inv]
    exact (regAt_cst _ _ _).mul (ha z hz)

theorem sec_eq_spanBy : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ), Sec (σ.D₁ x) k = spanBy (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x '' σ.N k) := by
  intro σ x k
  haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R).2
  haveI : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : IsProper σ.A.hom := σ.ab.proper
  let e : Sp (σ.C x).R ⟶ (σ.C x).G.left := (η[(σ.C x).G] : 𝟙_ _ ⟶ (σ.C x).G).left
  have he : e ≫ (σ.C x).G.hom = 𝟙 _ := Over.w (η[(σ.C x).G] : 𝟙_ _ ⟶ (σ.C x).G)
  have hρ := injective_of_flat _ (σ.flat x)
  have hρf : σ.ρ x σ.f ≠ 0 := fun h => σ.hf (hρ (h.trans (map_zero _).symm))
  have hc := theta_comp σ x
  have hc₀ : Function.Injective σ.c₀ := by
    apply Function.Injective.of_comp (f := σ.θ x)
    rw [← RingHom.coe_comp, hc]
    exact (cst_injective _ e he).comp hρ
  obtain ⟨hld, hsec⟩ := GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R (σ.C x).R (σ.ρ x) (σ.flat x) σ.A.left (σ.C x).G.left (σ.V x).toScheme
    (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom (σ.V x).ι (σ.φ x) (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x)
    σ.D (σ.D₁ x) (σ.pull x)
  have hinv : ∀ y : σ.A.left, RegAt y (σ.c₀ σ.f)⁻¹ := fun y => by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away σ.f) σ.f
    have h : σ.c₀ σ.f = GlobalTheory.Desc.cst σ.A.hom u := by rw [Setup.c₀, cst_comp, hu]; rfl
    rw [h, ← map_units_inv]
    exact regAt_cst _ _ _
  let W : Ideal σ.R → Set σ.A.left.functionField := fun p => {u | ∀ h : p.IsPrime, u ∈ σ.W (⟨p, h⟩ : PrimeSpectrum σ.R)}
  have hW : ∀ y : Sp σ.R, W y.asIdeal = σ.W y := fun y => Set.ext fun u => ⟨fun h => h y.isPrime, fun h _ => h⟩
  let W₁ : Ideal (σ.C x).R → Set (σ.C x).G.left.functionField := fun q =>
    {v | ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ((σ.C x).G.hom z).asIdeal = q → RegAt z v}
  have key := GlobalTheory.T.ringHomCoeffSpanSet_sections_flat_baseChange_normal σ.R (σ.C x).R _ _ (σ.ρ x) σ.c₀ (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x) σ.f σ.hf (σ.flat x) hρ hc₀
    hc hld (Sec σ.D k) (fun y => ((k • σ.D).vanishesAt_zero y).regularAt) (fun a ha b hb y => (ha y).add (hb y))
    (fun r a ha y => (ha y).regAt_mul (regAt_cst _ _ _)) (fun a ha y => (ha y).regAt_mul (hinv y)) W W₁
    (fun p hp _ u => (GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ (⟨p, hp⟩ : PrimeSpectrum σ.R) u).imp fun m hm _ => hm)
    (fun p hp _ _ => by
      have h := W_closed σ (⟨p, hp⟩ : PrimeSpectrum σ.R)
      exact ⟨fun a ha b hb _ => h.1 a (ha hp) b (hb hp), fun r a ha _ => h.2.1 r a (ha hp),
        fun s hs a ha _ => h.2.2 s hs a (ha hp)⟩)
    (fun q hq h1 hfq v hv => by
      have hG : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ((σ.C x).G.hom z).asIdeal = q →
          (RegAt z v ↔ ∃ s, s ∉ q ∧ GlobalTheory.Desc.cst (σ.C x).G.hom s * v ∈
            spanBy (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x '' W (q.comap (σ.ρ x)))) := by
        rintro z hz rfl
        have h := (GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime σ x z hz).1 v hv
        rw [← hW] at h
        exact h
      obtain ⟨z, hz, hzq⟩ := exists_vert_over _ e he hρf q h1 hfq
      exact ⟨fun h => (hG z hz hzq).1 (h z hz hzq), fun h z' hz' hq' => (hG z' hz' hq').2 h⟩)
  have hN : σ.N k = {u | u ∈ Sec σ.D k ∧ ∀ p : Ideal σ.R, p.IsPrime → p.height = 1 → σ.f ∈ p → u ∈ W p} := by
    ext u
    refine and_congr_right fun _ => (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ u).trans ⟨fun h p hp h1 hf _ => ?_, fun h p h1 hf => ?_⟩
    · exact h (⟨p, hp⟩ : PrimeSpectrum σ.R) h1 hf
    · exact h p.asIdeal p.isPrime h1 hf p.isPrime
  rw [hN, key, ← hsec k]
  ext v
  refine (GlobalTheory.T.mem_cartierMultiple_chart_iff_regular_codimOne σ x k v).trans (and_congr_right fun _ => ⟨fun h q _ _ _ z hz _ => h z hz, fun h z hz => ?_⟩)
  exact h _ ((σ.C x).G.hom z).isPrime (height_of_vert _ hρf hz) hz.2 z hz rfl

end GlobalTheory.Desc.ChartSpan
