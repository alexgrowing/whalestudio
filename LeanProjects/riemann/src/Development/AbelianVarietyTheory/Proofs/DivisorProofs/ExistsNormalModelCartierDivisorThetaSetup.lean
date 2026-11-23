import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocTuplesThetaOfAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierOfOrders
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterLatticeOfGoodReductionTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitOrdersEffectiveCartierExtendFromGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.OrdGlue

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {M : RatModel o' Ω}

theorem val_generic {K : Type} [Field K] (γ : Ω →+* K) (s : Ω) : M.val (spMap γ ≫ M.pt) s = γ s := by
  have hs : s ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp γ M.pt (M.pt_specializes (closedPoint Ω) _) ⟨s, hs⟩
  rwa [RatModel.valLoc_eq_val, RatModel.val_pt] at h

theorem val_jK {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) {x : M.Z} (h : ξ (closedPoint V) ⤳ x)
    (a : M.Z.presheaf.stalk x) : M.val (jK V ≫ ξ) (M.stalkHom x a) = algebraMap V (FractionRing V)
      ((Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.stalkSpecializes h).hom a)) := by
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) ξ h (M.stalkEquiv x a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  simp [RatModel.valLoc]

theorem centre {X : Scheme.{0}} {x : X} {V : Type} [CommRing V] [IsLocalRing V] (g : X.presheaf.stalk x →+* V) [IsLocalHom g] :
    (spMap g ≫ X.fromSpecStalk x) (closedPoint V) = x := by
  refine (Scheme.Hom.comp_apply _ _ _).trans
    (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
  exact comap_closedPoint g

def toA {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {X : Scheme.{0}} (T : Trait F) (ξ : Sp T.V ⟶ X) : ATrait X where
  V := T.V
  complete := T.complete
  ϖ := T.ϖ
  irr := T.irr
  ξ := ξ

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem isLocallyNoetherian [ArithBase o' Ω] (M : RatModel o' Ω) : IsLocallyNoetherian M.Z := by
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  exact LocallyOfFiniteType.isLocallyNoetherian M.s

theorem exists_trait [CharZero Ω] (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (maximalIdeal V) V) (θ : M.Z.presheaf.stalk x →+* V) (hθ : Function.Injective θ) [IsLocalHom θ] :
    ∃ (T : Trait F) (f : V →+* T.V) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ ∧
      ∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a)) := by
  obtain ⟨T, f, γ, hf, hl, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_trait_moduli_of_stalk_completeDVR g n o ζ F o' Ω M y₀ x V hV θ hθ
  exact ⟨T, f, _, γ, hf, hl, centre (f.comp θ), h₂, h₃, h₁⟩

theorem exists_trait_centre [ArithBase o' Ω] (y₀ : Sp Ω ⟶ F.X) (x : M.Z) :
    ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  haveI := ArithBase.char (o := o') (Ω := Ω)
  haveI := isLocallyNoetherian M
  haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)
  obtain ⟨V, _, _, _, θ, ⟨hd, hc, -⟩, hi, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.Z.presheaf.stalk x)
  obtain ⟨T, f, ξ, γ, -, -, h₁, h₂, h₃, -⟩ := exists_trait y₀ x V hc θ hi
  exact ⟨T, ξ, γ, h₁, h₂, h₃⟩

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {a b : V} (h : f b ∣ f a) : b ∣ a := by
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | h'
  · by_cases ha : a = 0
    · simp [ha]
    obtain ⟨d, hd⟩ := h
    have h0 : f a ≠ 0 := (map_ne_zero_iff f hf).2 ha
    have h1 : f c * d = 1 := mul_left_cancel₀ h0 (by rw [← mul_assoc, ← map_mul, ← hd, mul_one])
    have hu : IsUnit c := isUnit_of_map_unit f c (IsUnit.of_mul_eq_one d h1)
    exact (hu.mul_right_dvd).2 dvd_rfl
  · exact h'

theorem mem_O_of_traits [ArithBase o' Ω] (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (s : Ω)
    (h : ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt →
      T.y = spMap γ ≫ y₀ → ξ (closedPoint T.V) = x → ∃ w : T.V, γ s = algebraMap T.V (FractionRing T.V) w) : s ∈ M.O x := by
  haveI := ArithBase.char (o := o') (Ω := Ω)
  haveI := isLocallyNoetherian M
  haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)
  haveI := (hN x).2
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := M.O x) s
  obtain ⟨a, rfl⟩ := (M.stalkEquiv x).surjective a
  obtain ⟨b, rfl⟩ := (M.stalkEquiv x).surjective b
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact nonZeroDivisors.ne_zero hb (map_zero _)
  have hb1 : M.stalkHom x b ≠ 0 := (map_ne_zero_iff _ (M.stalkHom_injective x)).2 hb0
  change M.stalkHom x a / M.stalkHom x b ∈ M.O x
  obtain ⟨c, rfl⟩ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr (M.Z.presheaf.stalk x) a b hb0 fun V _ _ _ hV θ hθ hl => by
    obtain ⟨T, f, ξ, γ, hf, hfl, h₁, h₂, h₃, h₄⟩ := exists_trait y₀ x V hV θ hθ
    obtain ⟨w, hw⟩ := h T ξ γ h₂ h₃ h₁
    refine dvd_of_map_dvd f hf ⟨w, IsFractionRing.injective T.V (FractionRing T.V) ?_⟩
    rw [map_mul, ← h₄, ← h₄, ← hw, ← map_mul]
    congr 1
    change _ = _ * (M.stalkHom x a / M.stalkHom x b)
    rw [mul_div_cancel₀ _ hb1]
  rw [map_mul, mul_div_cancel_left₀ _ hb1]
  exact (M.stalkEquiv x c).2

theorem glue : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (φ : InvFun ℤ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (y₀ : Sp Ω ⟶ F.X) (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (V : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = y₀) → ∀ (ι : ℕ) (K : Type) (Jk : K → Type) (t : ∀ k, Jk k → Ω), (∀ k, Nonempty (Jk k) → M.HasDiv (t k)) → (∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ y₀ → ξ (closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData M.Z, (∀ z ∈ D.idealSheaf.support, z ∉ V) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ y₀ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n o _ ζ F φ o' Ω _ _ _ _ M hN y₀ V v hV hv ι K Jk t hdiv hloc
  haveI := isLocallyNoetherian M
  have hpt : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact M.top_le_preimage_pt hV (x := w) trivial
  have hgen : ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt →
      (toA T ξ).GenIn V := fun T ξ γ h => by
    rintro _ ⟨w, rfl⟩
    have e : (jK T.V ≫ ξ) w = M.pt (spMap γ w) := by rw [h]; exact Scheme.Hom.comp_apply _ _ _
    exact e ▸ M.top_le_preimage_pt hV (x := spMap γ w) trivial
  refine Exists.elim (GlobalTheory.Poinc.TraitGlue.exists_effCartier_of_orders M.Z hN V
    (fun A a => ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), A = toA T ξ ∧
      jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ ∧ (a : ℝ) = ι * φ.evalZ T.β) ?_ ?_ ?_) fun D ⟨hD, hord⟩ => ?_
  rotate_right
  · refine ⟨D, hD, fun T ξ γ h₁ h₂ => ?_⟩
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ γ h₁ h₂ specializes_rfl
    exact ⟨a, ha, hord (toA T ξ) a (hgen T ξ γ h₁) ⟨T, ξ, γ, rfl, h₁, h₂, ha⟩⟩
  · rintro _ a hr ⟨T, ξ, γ, rfl, h₁, h₂, ha⟩
    have hr' : Set.range ξ ⊆ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    have e : jK T.V ≫ IsOpenImmersion.lift V.ι ξ hr' = spMap γ ≫ IsOpenImmersion.lift V.ι M.pt hpt := by
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, h₁]
    haveI := GlobalTheory.T.subsingleton_characterLattice_of_goodReduction_trait g n o ζ F T (IsOpenImmersion.lift V.ι ξ hr' ≫ v) (by
      rw [← Category.assoc, e, Category.assoc, hv _ (IsOpenImmersion.lift_fac _ _ _), h₂])
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  · intro η hη
    obtain ⟨T, ξ, γ, rfl, h₁, h₂⟩ := exists_trait_centre (M := M) y₀ η
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ γ h₁ h₂ specializes_rfl
    have hinj : Function.Injective (Scheme.stalkClosedPointTo ξ).hom := by
      refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
      have e := val_jK ξ specializes_rfl b
      rw [TopCat.Presheaf.stalkSpecializes_refl, h₁, val_generic] at e
      simp only [CommRingCat.hom_id, RingHom.id_apply] at e
      rw [hb, map_zero, map_eq_zero, map_eq_zero_iff _ (M.stalkHom_injective _)] at e
      exact e
    have hne : (maximalIdeal (M.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
      intro hb
      rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.2 hb)] at hη
      exact zero_ne_one hη
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exfalso
        rw [pow_zero, Ideal.span_singleton_one] at he
        have hle : (maximalIdeal (M.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≤
            maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb => (map_mem_nonunits_iff _ b).2 hb
        exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 (he ▸ hle))
      · exact h
    refine ⟨toA T ξ, a, e, ⟨rfl, hinj, he1, specializes_rfl, ?_⟩, hgen T ξ γ h₁, T, ξ, γ, rfl, h₁, h₂, ha⟩
    change Ideal.map ((Scheme.stalkClosedPointTo ξ).hom.comp
      (M.Z.presheaf.stalkSpecializes (specializes_refl (ξ (closedPoint T.V)))).hom) _ = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact he
  · intro x
    obtain ⟨k, hk⟩ := hloc x
    obtain ⟨T₀, ξ₀, γ₀, h₀, h₁, h₂⟩ := exists_trait_centre (M := M) y₀ x
    obtain ⟨_, -, -, j₁, -⟩ := hk T₀ ξ₀ γ₀ h₁ h₂ (specializes_of_eq h₀)
    obtain ⟨j₀, hj₀⟩ := hdiv k ⟨j₁⟩ x
    have hreg : t k j₀ ∈ M.O x := mem_O_of_traits hN y₀ x _ fun T ξ γ h₁ h₂ h₀ => by
      obtain ⟨a, -, hge, -⟩ := hk T ξ γ h₁ h₂ (specializes_of_eq h₀)
      obtain ⟨-, w, hw⟩ := hge j₀
      rw [h₁, val_generic] at hw
      exact ⟨_, hw⟩
    obtain ⟨f, hf⟩ := (M.stalkEquiv x).surjective ⟨_, hreg⟩
    have hf' : M.stalkHom x f = t k j₀ := congrArg Subtype.val hf
    refine ⟨f, ?_⟩
    rintro _ h a - ⟨T, ξ, γ, rfl, h₁, h₂, ha⟩
    change ξ (closedPoint T.V) ⤳ x at h
    obtain ⟨a', ha', hge, j, w', hw'⟩ := hk T ξ γ h₁ h₂ h
    obtain rfl : a = a' := by exact_mod_cast ha.trans ha'.symm
    obtain ⟨-, w, hw⟩ := hge j₀
    obtain ⟨q, hq⟩ := (M.stalkEquiv x).surjective ⟨_, hj₀.2 j⟩
    have hq' : M.stalkHom x q = t k j / t k j₀ := congrArg Subtype.val hq
    have e₁ := val_jK ξ h f
    have e₂ := val_jK ξ h (f * q)
    rw [hf', hw] at e₁
    rw [map_mul, hf', hq', mul_div_cancel₀ _ hj₀.1, hw', map_mul (M.Z.presheaf.stalkSpecializes h).hom,
      map_mul (Scheme.stalkClosedPointTo ξ).hom] at e₂
    have e₃ := IsFractionRing.injective T.V (FractionRing T.V) e₁
    have e₄ := IsFractionRing.injective T.V (FractionRing T.V) e₂
    rw [← e₃, mul_assoc] at e₄
    have hu : IsUnit w := isUnit_of_mul_isUnit_left (mul_left_cancel₀ (pow_ne_zero a T.irr.ne_zero) e₄ ▸ w'.isUnit)
    exact (congrArg (fun r => Ideal.span {r}) e₃.symm).trans (Ideal.span_singleton_mul_right_unit hu _)

end GlobalTheory.Poinc.OrdGlue

theorem GlobalTheory.Poinc.exists_model_divisor_of_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ X₁ : Setup F W8 i, ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W8 hW hTI X₁
  obtain ⟨ι, K, _, Jk, _, t, hι, ht, hloc⟩ := GlobalTheory.Poinc.exists_locTuples_theta_of_adm g n hg hn hodd F φ hφ W8 hW
    X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.big X₁.sharp X₁.gen
  obtain ⟨Y, πY, U₀, EE, FinalForm, hhom, hprop, hAdm, hEE, hdiv⟩ := GlobalTheory.T.exists_admissible_projective_theta_model_over_model X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big X₁.M X₁.projM K Jk t ht
  haveI := X₁.imm
  let V : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ i.opensRange
  have hV : Set.range (V.ι ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact w.2
  let v : V.toScheme ⟶ F.X := IsOpenImmersion.lift i (V.ι ≫ πY ≫ X₁.π) hV
  have hv : v ≫ i = V.ι ≫ πY ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
  have hpt : Y.pt ≫ πY ≫ X₁.π = spMap X₁.S.R.val.toRingHom ≫ X₁.u ≫ i := by
    have h : Y.pt ≫ πY = X₁.M.pt := hhom.trans (by
      rw [show spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom = 𝟙 _ from Spec.map_id _, Category.id_comp])
    rw [← Category.assoc, h, X₁.comp]
  have hcomp : ∀ x : Sp X₁.Ω₁ ⟶ V.toScheme, x ≫ V.ι = Y.pt → x ≫ v = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
    intro x hx
    rw [← cancel_mono i, Category.assoc, hv, ← Category.assoc, hx, hpt, Category.assoc]
  have hVne : (V : Set Y.Z).Nonempty := by
    obtain ⟨w⟩ : Nonempty (Sp X₁.Ω₁) := inferInstance
    refine ⟨Y.pt w, ?_⟩
    show (πY ≫ X₁.π) (Y.pt w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, hpt, ← Category.assoc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial
  obtain ⟨D, hsupp, hord⟩ := GlobalTheory.Poinc.OrdGlue.glue g n _ _ F φ X₁.o₁ X₁.Ω₁ Y hAdm.1.normal _ V v hVne hcomp ι K Jk t hdiv fun x => by
    obtain ⟨k, hk⟩ := hloc Y U₀ EE FinalForm hAdm hEE x
    refine ⟨k, fun T ξ γ h₁ h₂ => hk T ξ ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, ?_, ?_⟩⟩
    · rw [Category.assoc, IsOpenImmersion.lift_fac, h₁]
    · rw [h₂, Category.assoc, ← Category.assoc _ FinalForm.u₀, FinalForm.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
  refine ⟨ι, Y, πY, D, hι, hhom, hprop, hAdm.1.normal, fun y hy h => hsupp y hy ?_, fun T ξ hξ => ?_⟩
  · show (πY ≫ X₁.π) y ∈ Set.range i
    rwa [Scheme.Hom.comp_apply]
  have hr : Set.range (jK T.V ≫ ξ) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show (πY ≫ X₁.π) ((jK T.V ≫ ξ) w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, Category.assoc, hξ, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  refine GlobalTheory.T.traitOrders_effectiveCartier_extend_from_generic g n hn F φ hφ W8 hW X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp Y U₀ EE FinalForm hAdm.1 V v hcomp D ι hsupp hord T ξ
    ⟨IsOpenImmersion.lift V.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [Category.comp_id, ← cancel_mono i, Category.assoc, hv, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hξ]
