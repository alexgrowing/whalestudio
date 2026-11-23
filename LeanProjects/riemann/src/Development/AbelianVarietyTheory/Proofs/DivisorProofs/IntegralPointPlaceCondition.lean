import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.HtGen.RegOver

theorem mem_range_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {x : V.X}
    (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_horizPt_over {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : V.X.Opens) (z : V.X)
    (g : Γ(V.X, W)) (hz : z ∈ W) (hg : g ≠ 0) (hzg : z ∉ V.X.basicOpen g) (a : 𝓞 F) (ha : a ∈ (V.p z).asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      a ∈ v.asIdeal ∧ y ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ V.j ∧
      ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ V.X.basicOpen g ∧ below (y ≫ V.j) ∈ V.X.basicOpen g := by
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(V.X, U) := V.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral V.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(V.X, U), hU.fromSpec x ∈ V.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ V.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  refine ⟨v, e, V.pb.lift _ _ hw, yt, ?_, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩
  · have e₁ : V.p z = Spec.map (GlobalTheory.TrueGeo.HorizPt.strHom V.p U) (hU.primeIdealOf ⟨z, hzU⟩) := by
      rw [← fromSpec_str V.p hU]
      exact congrArg V.p (hU.fromSpec_primeIdealOf ⟨z, hzU⟩).symm
    rw [e₁] at ha
    have h₄ : algebraMap (𝓞 F) Γ(V.X, U) a ∈ 𝔪 := hle' ha
    rw [← h₂] at h₄
    by_contra hv
    refine (IsLocalRing.mem_maximalIdeal _).1 h₄ (GlobalTheory.TrueGeo.RegCrit.isUnit_of_one_le e _ ?_)
    rw [h₁ a, e.w_alg, ← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_eq_one_iff_notMem F v a).2 hv).ge
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

open GlobalTheory.TrueGeo.RegCrit in

theorem regAt_of_integral_values_over : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  intro F _ _ Y V l U f hgen hf x hx hl
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  have hlz : (l : 𝓞 F) ∈ (V.p z).asIdeal := by
    have hne : (V.p z).asIdeal ≠ ⊥ := fun h => by
      obtain ⟨z', rfl⟩ := mem_range_j V h
      exact (zeroAt_iff.1 hzero).2 ((unitAt_iff (inv_ne_zero hf0)).2 ⟨hzero.regAt, (inv_inv f).symm ▸ hgen z' hzU⟩)
    have hle : (V.p z).asIdeal ≤ (V.p x).asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous))
    have hmax : (V.p z).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal (R := 𝓞 F) (V.p z).isPrime hne
    rwa [hmax.eq_of_le (V.p x).isPrime.ne_top hle]
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hv, hy, hc, hW, hn, hu⟩ := exists_horizPt_over V _ z g hzW' hg0 hzg _ hlz
  have hle := hf v e y yt hv hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := hu
  have hb : below (y ≫ V.j) ∈ W₀ ⊓ U := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ V.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : TrueGeo.valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.HtGen.RegOver
