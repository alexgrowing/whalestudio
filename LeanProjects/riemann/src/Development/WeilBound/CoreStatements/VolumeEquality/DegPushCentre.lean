import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
