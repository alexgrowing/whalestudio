import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocModel

section Scheme

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isProper_of_coordTie {κ : Type} [Finite κ] {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ x) (s : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType s] [QuasiCompact s] :
    IsProper s := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : QuasiSeparated s := (quasiSeparated_iff_quasiSeparatedSpace s).2 inferInstance
  refine IsProper.of_valuativeCriterion s fun S => ?_
  let V : ValuationSubring S.K := (ValuationRing.valuation S.R S.K).valuationSubring
  have hV : ∀ a : S.R, algebraMap S.R S.K a ∈ V := fun a =>
    (ValuationRing.mem_integer_iff S.R S.K _).2 ⟨a, rfl⟩
  let f : S.R →+* V := (algebraMap S.R S.K).codRestrict V hV
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact IsFractionRing.injective S.R S.K (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := (ValuationRing.mem_integer_iff S.R S.K y).1 hy
      exact ⟨a, rfl⟩
  let eH : CommRingCat.of S.R ≅ CommRingCat.of V := (RingEquiv.ofBijective f hf).toCommRingCatIso
  have hc : eH.hom ≫ CommRingCat.ofHom (algebraMap V S.K) = CommRingCat.ofHom (algebraMap S.R S.K) := by
    ext a
    rfl
  have hc' : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap V S.K)) ≫ Spec.map eH.hom := by
    rw [← Spec.map_comp, hc]
  have hi : Spec.map eH.hom ≫ Spec.map eH.inv = 𝟙 _ := by
    rw [← Spec.map_comp, eH.inv_hom_id, Spec.map_id]
  have hi' : Spec.map eH.inv ≫ Spec.map eH.hom = 𝟙 _ := by
    rw [← Spec.map_comp, eH.hom_inv_id, Spec.map_id]
  obtain ⟨z, ⟨-, hz⟩, huniq⟩ := coord_point_extends X Ω ξ κ x hT S.K V S.i₁ (hall _)
  let L : S.commSq.LiftStruct :=
    { l := Spec.map eH.inv ≫ z
      fac_left := by
        rw [hc', Category.assoc, reassoc_of% hi, hz]
      fac_right := specZIsTerminal.hom_ext _ _ }
  refine ⟨⟨⟨L⟩, fun L' => ?_⟩⟩
  have h1 : Spec.map eH.hom ≫ L'.l = z := by
    refine huniq _ ⟨hall _, ?_⟩
    rw [← Category.assoc, ← hc']
    exact L'.fac_left
  apply CommSq.LiftStruct.ext
  change L'.l = Spec.map eH.inv ≫ z
  rw [← h1, reassoc_of% hi']

theorem exists_toSpec [IsLocallyNoetherian X] (hall : ∀ q : X, genPt ξ ⤳ q) (hG : IsCptGen ξ) {R : Type} [CommRing R]
    (f : R →+* Ω) (hreg : ∀ (a : R) (q : Cpt ξ), f a ∈ regAt ξ q) :
    ∃ t : X ⟶ Spec (CommRingCat.of R), ξ ≫ t = Spec.map (CommRingCat.ofHom f) ∧
      ∀ (p : Cpt ξ) (ρ : R →+* X.presheaf.stalk p.1), (∀ a, genMap ξ p (ρ a) = f a) →
        X.fromSpecStalk p.1 ≫ t = Spec.map (CommRingCat.ofHom ρ : CommRingCat.of R ⟶ X.presheaf.stalk p.1) := by
  let ev : Γ(X, ⊤) →+* Ω := (X.presheaf.germ ⊤ (genPt ξ) trivial ≫ CoordExtend.gpC ξ).hom
  have hev' : ∀ (r : X) (hr : genPt ξ ⤳ r) (hrU : r ∈ (⊤ : X.Opens)) (g : Γ(X, ⊤)),
      genMap ξ ⟨r, hr⟩ ((X.presheaf.germ ⊤ r hrU).hom g) = ev g := by
    intro r hr hrU g
    change (X.presheaf.germ ⊤ r hrU ≫ X.presheaf.stalkSpecializes hr ≫ CoordExtend.gpC ξ).hom g = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  have hev : ∀ (q : Cpt ξ) (g : Γ(X, ⊤)), genMap ξ q ((X.presheaf.germ ⊤ q.1 trivial).hom g) = ev g :=
    fun q g => hev' q.1 q.2 trivial g
  have hinj : Function.Injective ev := fun a b h =>
    RegSection.section_eq hG ⊤ (fun q _ => hall q) a b fun q _ =>
      (hev ⟨q, hall q⟩ a).trans (h.trans (hev ⟨q, hall q⟩ b).symm)
  have hsec : ∀ a : R, ∃ g : Γ(X, ⊤), ev g = f a := by
    intro a
    obtain ⟨g, hg, -⟩ := RegSection.existsUnique_section X Ω ξ hG ⊤ (fun q _ => hall q) (f a)
      ⟨genPt ξ, trivial⟩ (fun q _ => hreg a ⟨q, hall q⟩)
    exact ⟨g, (hev ⟨genPt ξ, hall _⟩ g).symm.trans (hg _ trivial)⟩
  choose φ' hφ' using hsec
  let φ : R →+* Γ(X, ⊤) :=
    { toFun := φ'
      map_one' := hinj (by rw [hφ', map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hφ', map_mul, map_mul, hφ', hφ'])
      map_zero' := hinj (by rw [hφ', map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hφ', map_add, map_add, hφ', hφ']) }
  refine ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, fun p ρ hρ => ?_⟩
  · have h0 : Spec.map (CoordExtend.gpC ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h1 : ξ ≫ X.toSpecΓ = Spec.map (X.presheaf.germ ⊤ (genPt ξ) trivial ≫ CoordExtend.gpC ξ) := by
      rw [Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, ← Category.assoc, h0]
    rw [← Category.assoc, h1, ← Spec.map_comp]
    congr 1
    ext a
    exact hφ' a
  · rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    congr 1
    ext a
    apply hG.inj p
    refine (hev p (φ' a)).trans ((hφ' a).trans (hρ a).symm)

end Scheme

end GlobalTheory.CompanionTheory.Ar.Flat.LocModel

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocModel

section Base

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_baseChange {R O : Type} [CommRing R] [CommRing O] [Algebra R O] (M : Submonoid R) [IsLocalization M O]
    [Algebra O Ω] (hall : ∀ q : X, genPt ξ ⤳ q) (hG : IsCptGen ξ) (t : X ⟶ Spec (CommRingCat.of R)) [IsProper t]
    (ht : ξ ≫ t = Spec.map (CommRingCat.ofHom ((algebraMap O Ω).comp (algebraMap R O))))
    (hst : ∀ (p : Cpt ξ) (ρ : R →+* X.presheaf.stalk p.1),
      (∀ a, genMap ξ p (ρ a) = algebraMap O Ω (algebraMap R O a)) →
        X.fromSpecStalk p.1 ≫ t = Spec.map (CommRingCat.ofHom ρ : CommRingCat.of R ⟶ X.presheaf.stalk p.1)) :
    ∃ (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X),
      IsProper s ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧
        (∀ q' : X', genPt ξ' ⤳ q') ∧
        (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧
        ∀ p : Cpt ξ, (∀ b : O, algebraMap O Ω b ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  let j : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R O))
  have : IsPreimmersion j := IsPreimmersion.of_isLocalization M
  have hcomp : ξ ≫ t = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ≫ j := by
    rw [ht, ← Spec.map_comp]
    rfl
  let ξ' := pullback.lift ξ (Spec.map (CommRingCat.ofHom (algebraMap O Ω))) hcomp
  have hg : ξ' ≫ pullback.fst t j = ξ := pullback.lift_fst _ _ _
  have hs : ξ' ≫ pullback.snd t j = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) := pullback.lift_snd _ _ _
  have hD : Dominates ξ' ξ (pullback.fst t j) (RingHom.id Ω) := PushLoc.dominates_id hg
  have hgp : pullback.fst t j (genPt ξ') = genPt ξ := hD.map_genPt
  have hall' : ∀ q' : (pullback t j : Scheme.{0}), genPt ξ' ⤳ q' := by
    intro q'
    refine ((pullback.fst t j).isEmbedding.isInducing.specializes_iff).1 ?_
    rw [hgp]
    exact hall _
  refine ⟨pullback t j, ξ', pullback.snd t j, pullback.fst t j, inferInstance, hs, hg,
    PushLoc.isCptGen_of hg hG, hall', fun p' p hp a => ?_, fun p hp => ?_⟩
  · have e : p = PushLoc.emb hD p' := Subtype.ext hp
    rw [e, PushLoc.regAt_emb hD p']
  · let E : X.presheaf.stalk p.1 ≃+* (genMap ξ p).range :=
      RingEquiv.ofBijective (genMap ξ p).rangeRestrict
        ⟨fun a b h => hG.inj p (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩
    let ρ : O →+* X.presheaf.stalk p.1 :=
      E.symm.toRingHom.comp ((algebraMap O Ω).codRestrict (genMap ξ p).range hp)
    have hρ : ∀ b, genMap ξ p (ρ b) = algebraMap O Ω b := fun b =>
      congrArg Subtype.val (E.apply_symm_apply ((algebraMap O Ω).codRestrict (genMap ξ p).range hp b))
    have h1 : X.fromSpecStalk p.1 ≫ t =
        Spec.map (CommRingCat.ofHom ρ : CommRingCat.of O ⟶ X.presheaf.stalk p.1) ≫ j := by
      rw [hst p (ρ.comp (algebraMap R O)) fun a => hρ _, ← Spec.map_comp]
      rfl
    let w := pullback.lift (X.fromSpecStalk p.1) _ h1
    refine ⟨⟨w (IsLocalRing.closedPoint _), hall' _⟩, ?_⟩
    have e : w ≫ pullback.fst t j = X.fromSpecStalk p.1 := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply w (pullback.fst t j) _).symm.trans ?_
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint

end Base

section Place

variable {F' : Type} [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F'))

noncomputable abbrev intAt : Subring F' := (v.valuation F').integer

theorem isUnit_intAt {a : intAt v} (h : v.valuation F' (a : F') = 1) : IsUnit a := by
  have h0 : (a : F') ≠ 0 := fun h' => by simp [h'] at h
  have hi : v.valuation F' (a : F')⁻¹ ≤ 1 := by rw [map_inv₀, h, inv_one]
  exact IsUnit.of_mul_eq_one (⟨(a : F')⁻¹, hi⟩ : intAt v) (Subtype.ext (mul_inv_cancel₀ h0))

noncomputable def intMap : 𝓞 F' →+* intAt v :=
  (algebraMap (𝓞 F') F').codRestrict (intAt v) fun a => v.valuation_le_one a

noncomputable instance : Algebra (𝓞 F') (intAt v) := (intMap v).toAlgebra

theorem coe_algebraMap_intAt (a : 𝓞 F') : ((algebraMap (𝓞 F') (intAt v) a : intAt v) : F') = algebraMap (𝓞 F') F' a :=
  rfl

instance : IsLocalization.AtPrime (intAt v) v.asIdeal where
  map_units := by
    rintro ⟨y, hy⟩
    apply isUnit_intAt
    rw [coe_algebraMap_intAt]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hy
  surj := by
    rintro ⟨a, ha⟩
    obtain ⟨n, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v a ha
    exact ⟨⟨n, d⟩, Subtype.ext e⟩
  exists_of_eq := by
    intro a b h
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    rw [coe_algebraMap_intAt, coe_algebraMap_intAt] at h'
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 F') F') h'

theorem isDVR_intAt : IsDiscreteValuationRing (intAt v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F') v.ne_bot (intAt v)

theorem irreducible_intAt {π : intAt v} (hπ : v.valuation F' (π : F') = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : v.valuation F' ((u : intAt v) : F') * v.valuation F' (((u⁻¹ : (intAt v)ˣ) : intAt v) : F') = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
    rw [hπ] at h1
    have h2 : v.valuation F' (((u⁻¹ : (intAt v)ˣ) : intAt v) : F') ≤ 1 := (u⁻¹ : (intAt v)ˣ).1.2
    have h3 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have h4 := mul_le_of_le_one_right' (a := WithZero.exp (-1 : ℤ)) h2
    rw [h1] at h4
    exact absurd h3 (not_lt.2 h4)
  · rintro a b rfl
    have h0 : ∀ c : intAt v, v.valuation F' (c : F') ≠ 0 → ∃ m : ℤ, m ≤ 0 ∧ v.valuation F' (c : F') = WithZero.exp m := by
      intro c hc
      refine ⟨WithZero.log _, ?_, (WithZero.exp_log hc).symm⟩
      have := c.2
      rw [← WithZero.exp_le_exp, WithZero.exp_log hc, WithZero.exp_zero]
      exact this
    have hab : v.valuation F' (a : F') * v.valuation F' (b : F') = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← Subring.coe_mul, hπ]
    have hne : WithZero.exp (-1 : ℤ) ≠ 0 := WithZero.exp_ne_zero
    obtain ⟨m, hm, ema⟩ := h0 a fun h => hne (by rw [← hab, h, zero_mul])
    obtain ⟨n, hn, emb⟩ := h0 b fun h => hne (by rw [← hab, h, mul_zero])
    rw [ema, emb, ← WithZero.exp_add, WithZero.exp_inj] at hab
    obtain rfl | rfl : m = 0 ∨ n = 0 := by omega
    · exact Or.inl (isUnit_intAt v (by rw [ema, WithZero.exp_zero]))
    · exact Or.inr (isUnit_intAt v (by rw [emb, WithZero.exp_zero]))

end Place

theorem exists_localisation : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  intro X Ω _ ξ κ _ x F' _ _ ψ v π hall hT hN hπ
  obtain ⟨s₀, hft, hqc, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartFType.main X Ω ξ κ x hall hT
  have hprop : IsProper s₀ := isProper_of_coordTie hall hT s₀
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s₀
  obtain ⟨t, ht, hst⟩ := exists_toSpec hall hT.gen (ψ.comp (algebraMap (𝓞 F') F')) fun a q =>
    hN q _ ((map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe a)).tower_top)
  have htp : IsProper t := by
    have e : t ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 F'))) = s₀ := specZIsTerminal.hom_ext _ _
    have : IsProper (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 F')))) := e ▸ hprop
    exact IsProper.of_comp t (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 F'))))
  let alg : Algebra (intAt v) Ω := (ψ.comp (intAt v).subtype).toAlgebra
  have hmap : ∀ b : intAt v, algebraMap (intAt v) Ω b = ψ (b : F') := fun _ => rfl
  obtain ⟨X', ξ', s, g, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_baseChange (O := intAt v) v.asIdeal.primeCompl hall hT.gen t ht hst
  have hπ1 : v.valuation F' π ≤ 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  refine ⟨intAt v, inferInstance, inferInstance, isDVR_intAt v, alg, X', ξ', s, g, ⟨π, hπ1⟩, h1,
    irreducible_intAt v hπ, ?_, h2, h3, h4, h5, rfl, ?_, h6, fun p hp => h7 p fun b => hp _ b.2⟩
  · intro a b h
    exact Subtype.ext (ψ.injective h)
  · intro a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocModel
