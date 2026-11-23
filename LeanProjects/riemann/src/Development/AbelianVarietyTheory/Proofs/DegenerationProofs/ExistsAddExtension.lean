import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.AddExt

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {r : T ⟶ S} {r' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ r = r') (c d : Over.mk r ⟶ H) (c' d' : Over.mk r' ⟶ H) (hc : c'.left = g ≫ c.left)
    (hd : d'.left = g ≫ d.left) : (c' * d').left = g ≫ (c * d).left := by
  let u : Over.mk r' ⟶ Over.mk r := Over.homMk g hg
  have e₁ : c' = u ≫ c := Over.OverMorphism.ext hc
  have e₂ : d' = u ≫ d := Over.OverMorphism.ext hd
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem exists_common_geometric_point {X S S' : Scheme.{0}} (a : S ⟶ X) (a' : S' ⟶ X) (s : S) (s' : S')
    (h : a s = a' s') : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ S) (u' : Sp K ⟶ S'),
      u ≫ a = u' ≫ a' ∧ (∀ x, u x = s) ∧ (∀ x, u' x = s') := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback s s' h
  let k := (pullback a a').residueField z
  let w : Sp (AlgebraicClosure k) ⟶ pullback a a' :=
    spMap (algebraMap k (AlgebraicClosure k)) ≫ (pullback a a').fromSpecResidueField z
  have hw : ∀ x, w x = z := fun x => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨AlgebraicClosure k, inferInstance, inferInstance, w ≫ pullback.fst _ _, w ≫ pullback.snd _ _,
    by rw [Category.assoc w, Category.assoc w, pullback.condition], fun x => ?_, fun x => ?_⟩
  · rw [Scheme.Hom.comp_apply, hw, hz]
  · rw [Scheme.Hom.comp_apply, hw, hz']

theorem natCast_eq_zero_of_closedPoint (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (u : Sp K ⟶ Sp (OO p))
    (hu : ∀ x, u x = cPt p) : (p : K) = 0 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective u
  have h1 : (p : OO p) ∈ IsLocalRing.maximalIdeal (OO p) := by
    rw [Valuation.mem_maximalIdeal_iff]
    have : ((p : OO p) : PadicAlgCl p) = p := by simp
    rw [this, PadicAlgCl.valuation_p, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h2 := congrArg PrimeSpectrum.asIdeal (hu (⊥ : PrimeSpectrum K))
  have h3 : (p : OO p) ∈ Ideal.comap φ.hom (⊥ : Ideal K) := by
    have : Ideal.comap φ.hom (⊥ : Ideal K) = IsLocalRing.maximalIdeal (OO p) := h2
    rw [this]; exact h1
  simpa using h3

theorem prime_eq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] {K : Type} [Field K] (u : Sp K ⟶ Sp (OO p))
    (u' : Sp K ⟶ Sp (OO q)) (hu : ∀ x, u x = cPt p) (hu' : ∀ x, u' x = cPt q) : p = q := by
  have h1 := natCast_eq_zero_of_closedPoint p u hu
  have h2 := natCast_eq_zero_of_closedPoint q u' hu'
  have := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h1
  have := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).2 h2
  exact CharP.eq K ‹CharP K p› ‹CharP K q›

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (OO p).subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (OO p).subtype_injective]
  exact bot_le

theorem isPullback_a (C : Core) : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  refine ⟨⟨by simpa using C.cart.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by simpa using s.condition)) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [← cancel_mono C.G.ι, Category.assoc, IsPullback.lift_fst]
  · rw [IsPullback.lift_snd]
  · apply C.cart.hom_ext
    · rw [IsPullback.lift_fst, ← h1, Category.assoc]
    · rw [IsPullback.lift_snd, h2]

theorem eq_mul_of_generic (C : Core) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c d : Over.mk (spMap τ.j) ⟶ τ.H) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (hc : a₀ ≫ (fst C.A C.A).left ≫ C.a = gPt p ≫ c.left ≫ τ.f)
    (hd : a₀ ≫ (snd C.A C.A).left ≫ C.a = gPt p ≫ d.left ≫ τ.f)
    (b : Sp (OO p) ⟶ C.P.left) (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = y) :
    b = (c * d).left ≫ τ.f ≫ C.G.ι := by
  have := isDominant_gPt p
  have := C.proper
  have hA := isPullback_a C
  have : IsOpenImmersion C.a := MorphismProperty.of_isPullback hA.flip inferInstance
  have hinj : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  let k : Sp (PadicAlgCl p) ⟶ Sp (FractionRing τ.V) := spMap (IsFractionRing.lift hinj)
  have hk : k ≫ Out.jK τ.V = gPt p ≫ spMap τ.j := by
    simp only [k, ← Spec.map_comp]
    congr 1
    ext x
    simp
  refine ext_of_isDominant_of_isSeparated C.P.hom ?_ (gPt p) ?_
  · have h1 : τ.f ≫ C.G.ι ≫ C.P.hom = τ.H.hom ≫ τ.y₀ := τ.f_over
    have h2 : (c * d).left ≫ τ.H.hom = spMap τ.j := Over.w _
    rw [hb', Category.assoc, Category.assoc, h1, reassoc_of% h2, τ.fac]
  have wc : c.left ≫ τ.H.hom = spMap τ.j := Over.w _
  have wd : d.left ≫ τ.H.hom = spMap τ.j := Over.w _
  let c' : Over.mk k ⟶ (Over.pullback (Out.jK τ.V)).obj τ.H :=
    Over.homMk (pullback.lift (gPt p ≫ c.left) k (by rw [hk, Category.assoc, wc])) (pullback.lift_snd _ _ _)
  let d' : Over.mk k ⟶ (Over.pullback (Out.jK τ.V)).obj τ.H :=
    Over.homMk (pullback.lift (gPt p ≫ d.left) k (by rw [hk, Category.assoc, wd])) (pullback.lift_snd _ _ _)
  have hc' : c'.left ≫ pullback.fst τ.H.hom (Out.jK τ.V) = gPt p ≫ c.left := pullback.lift_fst _ _ _
  have hd' : d'.left ≫ pullback.fst τ.H.hom (Out.jK τ.V) = gPt p ≫ d.left := pullback.lift_fst _ _ _
  let c₁ : Over.mk (k ≫ Out.jK τ.V) ⟶ τ.H := Over.homMk (gPt p ≫ c.left) (by simp [hk, wc])
  let d₁ : Over.mk (k ≫ Out.jK τ.V) ⟶ τ.H := Over.homMk (gPt p ≫ d.left) (by simp [hk, wd])
  have e₁ : (c₁ * d₁).left = (c' * d').left ≫ pullback.fst τ.H.hom (Out.jK τ.V) :=
    (isGrpPullback_pullback τ.H (Out.jK τ.V)).2 (Over.mk k) c' d' c₁ d₁ hc'.symm hd'.symm
  have e₂ : (c₁ * d₁).left = gPt p ≫ (c * d).left := mul_left_comp (gPt p) hk.symm c d c₁ d₁ rfl rfl
  have wφ : τ.φ ≫ C.A.hom = pullback.snd τ.H.hom (Out.jK τ.V) ≫ τ.yK := τ.φ_cart.1.w
  have wc' : c'.left ≫ pullback.snd τ.H.hom (Out.jK τ.V) = k := pullback.lift_snd _ _ _
  have wd' : d'.left ≫ pullback.snd τ.H.hom (Out.jK τ.V) = k := pullback.lift_snd _ _ _
  let c₂ : Over.mk (k ≫ τ.yK) ⟶ C.A := Over.homMk (c'.left ≫ τ.φ)
    (by change (c'.left ≫ τ.φ) ≫ C.A.hom = k ≫ τ.yK; rw [Category.assoc, wφ, reassoc_of% wc'])
  let d₂ : Over.mk (k ≫ τ.yK) ⟶ C.A := Over.homMk (d'.left ≫ τ.φ)
    (by change (d'.left ≫ τ.φ) ≫ C.A.hom = k ≫ τ.yK; rw [Category.assoc, wφ, reassoc_of% wd'])
  have e₃ : (c₂ * d₂).left = (c' * d').left ≫ τ.φ := τ.φ_cart.2 (Over.mk k) c' d' c₂ d₂ rfl rfl
  have e₄ : (lift c₂ d₂).left = a₀ := by
    apply pullback.hom_ext
    · have h1 : (lift c₂ d₂).left ≫ (fst C.A C.A).left = c'.left ≫ τ.φ := by
        rw [← Over.comp_left, lift_fst]; rfl
      change _ ≫ (fst C.A C.A).left = _ ≫ (fst C.A C.A).left
      rw [h1, ← cancel_mono C.a, Category.assoc, Category.assoc, hc, τ.φ_f, reassoc_of% hc']
    · have h1 : (lift c₂ d₂).left ≫ (snd C.A C.A).left = d'.left ≫ τ.φ := by
        rw [← Over.comp_left, lift_snd]; rfl
      change _ ≫ (snd C.A C.A).left = _ ≫ (snd C.A C.A).left
      rw [h1, ← cancel_mono C.a, Category.assoc, Category.assoc, hd, τ.φ_f, reassoc_of% hd']
  have e₅ : a₀ ≫ (μ[C.A]).left = (c' * d').left ≫ τ.φ := by
    rw [← e₃, ← e₄, ← Over.comp_left]; rfl
  rw [hb, reassoc_of% e₅, reassoc_of% τ.φ_f, ← reassoc_of% e₂, e₁, Category.assoc]

theorem isPullback_square (C : Core) (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) :
    IsPullback φ₂ (C.A ⊗ C.A).hom (C.GG ⊗ C.GG).hom C.U.ι := by
  have hA := isPullback_a C
  have : IsOpenImmersion C.a := MorphismProperty.of_isPullback hA.flip inferInstance
  have w₁ : (fst C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have w₂ : (snd C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have v₁ : (fst C.A C.A).left ≫ C.A.hom = (C.A ⊗ C.A).hom := Over.w _
  have v₂ : (snd C.A C.A).left ≫ C.A.hom = (C.A ⊗ C.A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst C.GG C.GG).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd C.GG C.GG).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst C.GG C.GG).left = _ ≫ (fst C.GG C.GG).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ C.a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd C.GG C.GG).left = _ ≫ (snd C.GG C.GG).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ C.a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ C.A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst C.A C.A).left = _
      rw [← cancel_mono C.a, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd C.A C.A).left = _
      rw [← cancel_mono C.a, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]

theorem isIntegral_and_normal (C : Core) [Smooth C.GG.hom] (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left)
    (h : IsSquare C.a φ₂) : IsIntegral (C.GG ⊗ C.GG).left ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (C.GG ⊗ C.GG).left ∧ Nonempty (C.A ⊗ C.A).left := by
  have hp := isPullback_square C φ₂ h
  have := C.lft
  have : Smooth (C.GG ⊗ C.GG).hom := inferInstanceAs (Smooth (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (C.GG ⊗ C.GG).left :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (C.GG ⊗ C.GG).hom C.normal
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : IsLocallyNoetherian (C.GG ⊗ C.GG).left := LocallyOfFiniteType.isLocallyNoetherian (C.GG ⊗ C.GG).hom
  have := C.ab.smooth
  have := C.ab.geomConnected
  have : Nonempty C.U := ⟨⟨_, C.ne.some_mem⟩⟩
  have : ConnectedSpace C.A.left := GeometricallyConnected.connectedSpace C.A.hom C.A.hom.isOpenMap
  have hc : ConnectedSpace (C.A ⊗ C.A).left := inferInstanceAs (ConnectedSpace ↥(pullback C.A.hom C.A.hom))
  have hr : Set.range φ₂ = (C.GG ⊗ C.GG).hom ⁻¹' C.U := by
    rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Function.Surjective.range_comp hp.isoPullback.hom.surjective, Scheme.Pullback.range_fst,
      Scheme.Opens.range_ι]
  have hd : Dense (Set.range φ₂) := by
    rw [hr]
    exact (C.U.isOpen.dense C.ne).preimage (C.GG ⊗ C.GG).hom.isOpenMap
  have : ConnectedSpace (C.GG ⊗ C.GG).left := by
    have h : _root_.IsConnected (closure (Set.range φ₂)) := (isConnected_range φ₂.continuous).closure
    rw [hd.closure_eq] at h
    exact connectedSpace_iff_univ.mpr h
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace _, hN, inferInstance⟩

theorem exists_test (C : Core) (hT : C.HasTests) (hC : C.TestCart)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p : ℕ} [Fact p.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom) :
    ∃ (τ : C.Test (a ≫ (C.GG ⊗ C.GG).hom)) (c d : Over.mk (spMap τ.j) ⟶ τ.H),
      c.left ≫ τ.f = a ≫ (fst C.GG C.GG).left ∧ d.left ≫ τ.f = a ≫ (snd C.GG C.GG).left ∧
      b = (c * d).left ≫ τ.f ≫ C.G.ι := by
  have hp := isPullback_square C φ₂ h
  have w₁ : (fst C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have w₂ : (snd C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have hcl : C.Cl (a ≫ (C.GG ⊗ C.GG).hom) := by
    rintro _ ⟨x, rfl⟩
    rw [← reassoc_of% ha, hp.w, ← Category.assoc, Scheme.Hom.comp_apply]
    exact Subtype.property _
  obtain ⟨τ⟩ := hT p _ hcl
  have hτ := hC p _ τ
  let c : Over.mk (spMap τ.j) ⟶ τ.H := Over.homMk
    (hτ.lift (a ≫ (fst C.GG C.GG).left) (spMap τ.j) (by rw [Category.assoc, w₁, τ.fac])) (hτ.lift_snd _ _ _)
  let d : Over.mk (spMap τ.j) ⟶ τ.H := Over.homMk
    (hτ.lift (a ≫ (snd C.GG C.GG).left) (spMap τ.j) (by rw [Category.assoc, w₂, τ.fac])) (hτ.lift_snd _ _ _)
  have hc : c.left ≫ τ.f = a ≫ (fst C.GG C.GG).left := hτ.lift_fst _ _ _
  have hd : d.left ≫ τ.f = a ≫ (snd C.GG C.GG).left := hτ.lift_fst _ _ _
  refine ⟨τ, c, d, hc, hd, eq_mul_of_generic C τ c d a₀ ?_ ?_ b hb hb'⟩
  · rw [hc, ← reassoc_of% ha, h.1]
  · rw [hd, ← reassoc_of% ha, h.2]

theorem range_comp_test {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) {K : Type}
    [Field K] (u : Sp K ⟶ Sp (OO p)) (hu : ∀ x, u x = cPt p) :
    Set.range (u ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
  have := τ.j_loc
  have h : ∀ x, (u ≫ spMap τ.j) x = IsLocalRing.closedPoint τ.V := fun x => by
    rw [Scheme.Hom.comp_apply, hu]
    exact IsLocalRing.comap_closedPoint τ.j
  ext z
  exact ⟨fun ⟨x, hx⟩ => hx ▸ h x, fun hz => ⟨(⊥ : PrimeSpectrum K), (h _).trans hz.symm⟩⟩

theorem centre_eq (C : Core) (hT : C.HasTests) (hC : C.TestCart) (hF : C.FibLaw)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom)
    (a' : Sp (OO q) ⟶ (C.GG ⊗ C.GG).left) (a₁ : Sp (PadicAlgCl q) ⟶ (C.A ⊗ C.A).left)
    (ha' : a₁ ≫ φ₂ = gPt q ≫ a') (b' : Sp (OO q) ⟶ C.P.left)
    (hb₁ : gPt q ≫ b' = a₁ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb₁' : b' ≫ C.P.hom = a' ≫ (C.GG ⊗ C.GG).hom)
    (e : a (cPt p) = a' (cPt q)) : b (cPt p) = b' (cPt q) := by
  obtain ⟨K, _, _, u, u', hu, h1, h2⟩ := exists_common_geometric_point a a' _ _ e
  obtain rfl := prime_eq p q u u' h1 h2
  obtain ⟨τ, c, d, hc, hd, rfl⟩ := exists_test C hT hC φ₂ h a a₀ ha b hb hb'
  obtain ⟨τ', c', d', hc', hd', rfl⟩ := exists_test C hT hC φ₂ h a' a₁ ha' b' hb₁ hb₁'
  let v : Over.mk (u ≫ spMap τ.j) ⟶ Over.mk (spMap τ.j) := Over.homMk u
  let v' : Over.mk (u' ≫ spMap τ'.j) ⟶ Over.mk (spMap τ'.j) := Over.homMk u'
  have key := (hF p _ _ τ τ' K (u ≫ spMap τ.j) (u' ≫ spMap τ'.j) (range_comp_test τ u h1)
    (range_comp_test τ' u' h2) (by rw [Category.assoc, Category.assoc, τ.fac, τ'.fac, reassoc_of% hu])
    (v ≫ c) (v ≫ d) (v' ≫ c') (v' ≫ d')
    (by
      change (u ≫ c.left) ≫ _ = (u' ≫ c'.left) ≫ _
      rw [Category.assoc, Category.assoc, hc, hc', reassoc_of% hu])
    (by
      change (u ≫ d.left) ≫ _ = (u' ≫ d'.left) ≫ _
      rw [Category.assoc, Category.assoc, hd, hd', reassoc_of% hu])).1
  rw [← MonObj.comp_mul, ← MonObj.comp_mul] at key
  have key' : u ≫ (c * d).left ≫ τ.f ≫ C.G.ι = u' ≫ (c' * d').left ≫ τ'.f ≫ C.G.ι := by
    have : (u ≫ (c * d).left) ≫ τ.f = (u' ≫ (c' * d').left) ≫ τ'.f := key
    simpa only [Category.assoc] using congrArg (· ≫ C.G.ι) this
  obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
  have := congrArg (fun g : Sp K ⟶ C.P.left => g x) key'
  beta_reduce at this
  rwa [Scheme.Hom.comp_apply u, Scheme.Hom.comp_apply u', h1, h2] at this

end GlobalTheory.ZJ.AddExt

namespace GlobalTheory.ZJ
open AddExt

theorem Core.exists_add_extension : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a := by
  intro C hT hS hC hF
  have hA := isPullback_a C
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  let φ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left :=
    pullback.map C.A.hom C.A.hom C.GG.hom C.GG.hom C.a C.a C.U.ι hA.w.symm hA.w.symm
  have hφ : IsSquare C.a φ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hp := isPullback_square C φ hφ
  have : IsOpenImmersion φ := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨hI, hN, ⟨x₀⟩⟩ := isIntegral_and_normal C φ hφ
  have := C.lft
  have := C.qc
  have := C.flat
  have := C.proper
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : QuasiCompact C.GG.hom := inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom))
  have : Smooth (C.GG ⊗ C.GG).hom := inferInstanceAs (Smooth (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom))
  have : QuasiCompact (C.GG ⊗ C.GG).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom))
  have wμ : (μ[C.A]).left ≫ C.A.hom = (C.A ⊗ C.A).hom := Over.w _
  obtain ⟨Φ, ⟨hΦ, hΦ'⟩, -⟩ := existsUnique_extension_of_finite_specializations (C.GG ⊗ C.GG).left
    ((C.GG ⊗ C.GG).hom ≫ C.π) hN C.Z C.P.left (C.GG ⊗ C.GG).hom C.P.hom C.G φ.opensRange
    (φ.isoOpensRange.inv ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) ⟨_, x₀, rfl⟩
    (by
      have := C.cart.w
      rw [← φ.isoOpensRange_inv_comp]
      simp only [Category.assoc] at this ⊢
      rw [this, reassoc_of% wμ, hp.w])
    (fun σ _ => by
      refine ⟨{w | ∃ (p : ℕ) (_ : Fact p.Prime) (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left)
        (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left) (b : Sp (OO p) ⟶ C.P.left), a (cPt p) = σ ∧
        a₀ ≫ φ = gPt p ≫ a ∧ gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι ∧
        b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom ∧ b (cPt p) = w}, Set.Subsingleton.finite ?_, ?_, ?_⟩
      · rintro _ ⟨p, _, a, a₀, b, h1, h2, h3, h4, rfl⟩ _ ⟨q, _, a', a₁, b', h1', h2', h3', h4', rfl⟩
        exact centre_eq C hT hC hF φ hφ a a₀ h2 b h3 h4 a' a₁ h2' b' h3' h4' (h1.trans h1'.symm)
      · rintro _ ⟨p, _, a, a₀, b, h1, h2, h3, h4, rfl⟩
        obtain ⟨τ, c, d, -, -, rfl⟩ := exists_test C hT hC φ hφ a a₀ h2 b h3 h4
        rw [← Category.assoc, Scheme.Hom.comp_apply]
        exact Subtype.property _
      · intro p _ a a₀ b h1 h2 h3 h4
        refine ⟨p, inferInstance, a, a₀ ≫ φ.isoOpensRange.inv, b, h1, ?_, ?_, h4, rfl⟩
        · rw [Category.assoc, φ.isoOpensRange_inv_comp, h2]
        · rw [Category.assoc, h3])
  refine ⟨Over.homMk Φ hΦ', fun φ₂ h₂ => ?_⟩
  obtain rfl : φ₂ = φ := pullback.hom_ext (h₂.1.trans hφ.1.symm) (h₂.2.trans hφ.2.symm)
  change φ ≫ Φ = _
  rw [← cancel_mono C.G.ι, Category.assoc, Category.assoc, ← φ.isoOpensRange_hom_ι, Category.assoc, hΦ,
    Iso.hom_inv_id_assoc]

end GlobalTheory.ZJ
