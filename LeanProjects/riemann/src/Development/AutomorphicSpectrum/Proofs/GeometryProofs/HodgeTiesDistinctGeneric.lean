import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt

open Limits

theorem surjectiveOnStalks_spMap {O F : Type} [CommRing O] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (β : O →+* F) (h : Mono (spMap β)) : SurjectiveOnStalks (spMap β) := by
  rw [SurjectiveOnStalks.Spec_iff]
  have g := (GlobalTheory.OneArcCompare.mono_spMap_iff β).1 h
  refine RingHom.surjectiveOnStalks_iff_forall_maximal'.2 fun I hI s => ?_
  have hb : I = ⊥ := (Ideal.eq_bot_or_top I).resolve_right hI.ne_top
  subst hb
  obtain ⟨p, q, hq, e⟩ := g s
  refine ⟨p, q, 1, by simp, by simpa using hq, ?_⟩
  simpa [mul_comm] using e

theorem isEmbedding_fst {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] (s : X ⟶ Sp O) (β : O →+* F)
    [SurjectiveOnStalks (spMap β)] : IsEmbedding (pullback.fst s (spMap β)) := by
  have hL := SurjectiveOnStalks.isEmbedding_pullback s (spMap β)
  let t₀ : Sp F := IsLocalRing.closedPoint F
  have e : (fun x => (pullback.fst s (spMap β) x, pullback.snd s (spMap β) x)) =
      (fun a : X => (a, t₀)) ∘ (pullback.fst s (spMap β)) := by
    funext x
    exact Prod.ext rfl (Subsingleton.elim (α := PrimeSpectrum F) _ _)
  rw [e] at hL
  exact (IsEmbedding.of_comp_iff (isEmbedding_prodMkLeft t₀)).1 hL

theorem exists_maximal_generisation {P : Type} [TopologicalSpace P] [T0Space P] [QuasiSober P] (x : P) :
    ∃ m, m ⤳ x ∧ ∀ m', m' ⤳ m → m' = m := by
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  refine ⟨hCi.genericPoint, hgen.specializes mem_irreducibleComponent, fun m' hm' => ?_⟩
  have hmax := irreducibleComponent_mem_irreducibleComponents x
  have hsub : irreducibleComponent x ⊆ closure {m'} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.1 hm') isClosed_closure
  have hle := hmax.2 (isIrreducible_singleton.closure) hsub
  have hm'C : m' ∈ irreducibleComponent x := hle (subset_closure rfl)
  exact (hm'.antisymm (hgen.specializes hm'C)).eq

theorem exists_equiv_of_pts {X : Scheme.{0}} {K₁ K₂ : Type} [Field K₁] [Field K₂] (x₁ : Sp K₁ ⟶ X) (x₂ : Sp K₂ ⟶ X)
    (h : genPt x₁ = genPt x₂) (b₁ : Function.Bijective (Scheme.stalkClosedPointTo x₁).hom)
    (b₂ : Function.Bijective (Scheme.stalkClosedPointTo x₂).hom) :
    ∃ ψ : K₂ ≃+* K₁, spMap ψ.toRingHom ≫ x₂ = x₁ := by
  have key : ∀ p, genPt x₁ = p → ∃ a : X.presheaf.stalk p ⟶ CommRingCat.of K₁,
      Function.Bijective a.hom ∧ Spec.map a ≫ X.fromSpecStalk p = x₁ := by
    rintro _ rfl
    exact ⟨_, b₁, Scheme.Spec_stalkClosedPointTo_fromSpecStalk x₁⟩
  obtain ⟨a, ha, ea⟩ := key _ h
  let e₁ := RingEquiv.ofBijective a.hom ha
  let e₂ := RingEquiv.ofBijective (Scheme.stalkClosedPointTo x₂).hom b₂
  refine ⟨e₂.symm.trans e₁, ?_⟩
  have e : Scheme.stalkClosedPointTo x₂ ≫ CommRingCat.ofHom (e₂.symm.trans e₁).toRingHom = a := by
    ext t
    show e₁ (e₂.symm (e₂ t)) = a.hom t
    rw [RingEquiv.symm_apply_apply]
    rfl
  calc spMap (e₂.symm.trans e₁).toRingHom ≫ x₂
      = spMap (e₂.symm.trans e₁).toRingHom ≫ Spec.map (Scheme.stalkClosedPointTo x₂) ≫
          X.fromSpecStalk (genPt x₂) := by
        rw [show Spec.map (Scheme.stalkClosedPointTo x₂) ≫ X.fromSpecStalk (genPt x₂) = x₂ from
          Scheme.Spec_stalkClosedPointTo_fromSpecStalk x₂]
    _ = Spec.map a ≫ X.fromSpecStalk (genPt x₂) := by
        refine Eq.trans ?_ (congrArg (· ≫ X.fromSpecStalk (genPt x₂)) (congrArg Spec.map e))
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecStalk (genPt x₂)) (Spec.map_comp _ _).symm)
    _ = x₁ := ea

theorem bijective_of_comp {W X : Scheme.{0}} (j : W ⟶ X) [SurjectiveOnStalks j] {K : Type} [Field K] (x : Sp K ⟶ W)
    (h : Function.Bijective (Scheme.stalkClosedPointTo (x ≫ j)).hom) :
    Function.Bijective (Scheme.stalkClosedPointTo x).hom := by
  have e : Scheme.stalkClosedPointTo (x ≫ j) = j.stalkMap _ ≫ Scheme.stalkClosedPointTo x :=
    Scheme.stalkClosedPointTo_comp x j
  rw [e] at h
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨a', rfl⟩ := j.stalkMap_surjective _ a
    obtain ⟨b', rfl⟩ := j.stalkMap_surjective _ b
    exact congrArg _ (h.1 hab)
  · obtain ⟨a, rfl⟩ := h.2 t
    exact ⟨_, rfl⟩

theorem bijective_comp_iso {W W' : Scheme.{0}} (r : W ⟶ W') [IsIso r] {K : Type} [Field K] (x : Sp K ⟶ W)
    (h : Function.Bijective (Scheme.stalkClosedPointTo x).hom) :
    Function.Bijective (Scheme.stalkClosedPointTo (x ≫ r)).hom := by
  have e : Scheme.stalkClosedPointTo (x ≫ r) = r.stalkMap _ ≫ Scheme.stalkClosedPointTo x :=
    Scheme.stalkClosedPointTo_comp x r
  rw [e]
  exact h.comp (ConcreteCategory.bijective_of_isIso (r.stalkMap _))

theorem exists_perm {W X : Scheme.{0}} (j : W ⟶ X) (hj : IsEmbedding j) {C : Type} [Finite C] (pt : C → W)
    (hinj : Function.Injective fun k => j (pt k)) (hmax : ∀ k (q : X), q ⤳ j (pt k) → q = j (pt k))
    (hall : ∀ q : X, (∀ q', q' ⤳ q → q' = q) → ∃ k, j (pt k) = q) (r : W ≅ W) :
    ∃ π : Equiv.Perm C, ∀ k, pt (π k) = r.hom (pt k) := by
  have hi : ∀ w, r.inv (r.hom w) = w := fun w => by
    rw [← Scheme.Hom.comp_apply, r.hom_inv_id]
    rfl
  have hi' : ∀ w, r.hom (r.inv w) = w := fun w => by
    rw [← Scheme.Hom.comp_apply, r.inv_hom_id]
    rfl
  have hW : ∀ k (u : W), u ⤳ pt k → u = pt k := fun k u hu =>
    hj.injective (hmax k _ (hu.map j.continuous))
  have hex : ∀ k, ∃ k', pt k' = r.hom (pt k) := by
    intro k
    obtain ⟨m, hm, hm'⟩ := exists_maximal_generisation (j (r.hom (pt k)))
    obtain ⟨k', rfl⟩ := hall m hm'
    refine ⟨k', ?_⟩
    have h1 : pt k' ⤳ r.hom (pt k) := hj.isInducing.specializes_iff.1 hm
    have h2 : r.inv (pt k') ⤳ pt k := by
      have := h1.map r.inv.continuous
      rwa [hi] at this
    have h3 := hW k _ h2
    rw [← h3, hi']
  choose π hπ using hex
  have hπi : Function.Injective π := by
    intro a b hab
    have h1 : r.hom (pt a) = r.hom (pt b) := by rw [← hπ a, ← hπ b, hab]
    have h2 : pt a = pt b := by
      have := congrArg r.inv h1
      rwa [hi, hi] at this
    exact hinj (congrArg j h2)
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπi), hπ⟩

theorem exists_lift {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (s : X ⟶ Sp O) (hs : IsProjOver s) (β : O →+* F) (hβ : Mono (spMap β))
    {W : Scheme.{0}} (jQ : W ⟶ pullback s (spMap β)) [IsOpenImmersion jQ] (hd : Dense (Set.range jQ))
    {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (hover : spMap fn ≫ ξ₀ ≫ s = spMap (cst.comp β)) :
    ∃ x : Sp Ω₀ ⟶ W, x ≫ jQ ≫ pullback.fst _ _ = ξ₀ ∧ spMap fn ≫ x ≫ jQ ≫ pullback.snd _ _ = spMap cst ∧
      Function.Bijective (Scheme.stalkClosedPointTo x).hom := by
  have hsurj := surjectiveOnStalks_spMap β hβ
  have hgen := (GlobalTheory.OneArcCompare.mono_spMap_iff β).1 hβ
  let g : O →+* Ω₀ := (Spec.preimage (ξ₀ ≫ s)).hom
  have hs' : ξ₀ ≫ s = spMap g := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (ξ₀ ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomp : fn.comp g = cst.comp β := by
    have h1 : spMap (fn.comp g) = spMap (cst.comp β) := by
      rw [← hover, hs']
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hc : ∀ t, fn (g t) = cst (β t) := fun t => RingHom.congr_fun hcomp t
  have hr : ∀ u, cst u ∈ fn.range := by
    intro u
    obtain ⟨p, q, hq, e⟩ := hgen u
    have hq' : cst (β q) ≠ 0 := fun h0 => hq (cst.injective (by rw [h0, map_zero]))
    refine ⟨g p / g q, ?_⟩
    rw [map_div₀, hc, hc, ← e, map_mul, mul_div_cancel_right₀ _ hq']
  let eq : Ω₀ ≃+* fn.range := RingEquiv.ofBijective fn.rangeRestrict
    ⟨fun a b hab => fn.injective (congrArg Subtype.val hab), fn.rangeRestrict_surjective⟩
  let γ : F →+* Ω₀ := eq.symm.toRingHom.comp (cst.codRestrict fn.range hr)
  have hγ : ∀ u, fn (γ u) = cst u := fun u =>
    congrArg Subtype.val (eq.apply_symm_apply (cst.codRestrict fn.range hr u))
  have hγg : γ.comp β = g := RingHom.ext fun t => fn.injective (by
    show fn (γ (β t)) = fn (g t)
    rw [hγ, hc])
  have hγc : fn.comp γ = cst := RingHom.ext hγ
  let w : Sp Ω₀ ⟶ pullback s (spMap β) := pullback.lift ξ₀ (spMap γ) (by
    rw [hs', ← hγg]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp])
  have hwf : w ≫ pullback.fst _ _ = ξ₀ := pullback.lift_fst _ _ _
  have hws : w ≫ pullback.snd _ _ = spMap γ := pullback.lift_snd _ _ _
  have hemb := isEmbedding_fst s β
  have hnoeth := HodgeBasic.noetherianSpace_pullback hs β
  have hran : Set.range w ⊆ Set.range jQ := by
    rintro _ ⟨t, rfl⟩
    have hfw : pullback.fst s (spMap β) (w t) = genPt ξ₀ := by
      rw [← Scheme.Hom.comp_apply, hwf]
      exact congrArg ξ₀ (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _)
    refine HodgeBasic.mem_of_dense_of_maximal jQ.isOpenEmbedding.isOpen_range hd fun y' h' => ?_
    have h2 : pullback.fst s (spMap β) y' ⤳ genPt ξ₀ := hfw ▸ h'.map (pullback.fst s (spMap β)).continuous
    exact hemb.injective ((GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ h2).trans hfw.symm)
  have hfac : IsOpenImmersion.lift jQ w hran ≫ jQ = w := IsOpenImmersion.lift_fac _ _ _
  have e₁ : IsOpenImmersion.lift jQ w hran ≫ jQ ≫ pullback.fst _ _ = ξ₀ := by
    rw [reassoc_of% hfac, hwf]
  refine ⟨IsOpenImmersion.lift jQ w hran, e₁, ?_, ?_⟩
  · rw [reassoc_of% hfac, hws, ← hγc]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · have hfs : SurjectiveOnStalks (pullback.fst s (spMap β)) :=
      MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback s (spMap β)).flip hsurj
    refine bijective_of_comp (jQ ≫ pullback.fst _ _) _ ?_
    rw [e₁]
    exact h₀.bij

theorem exists_perm_isImageCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ) (C : Type) [Fintype C] (M : C → Top.RootModel (CMType H) (D.p + D.q)) (tie : ∀ k, HodgeTie Y S n (M k)), Mono (spMap β) → Function.Injective (fun k => genPt (tie k).A.ξ₀) → (∀ q : Y.X, (∀ q' : Y.X, q' ⤳ q → q' = q) → ∃ k, genPt (tie k).A.ξ₀ = q) → ∀ Φ : Xo.X ≅ Xo.X, Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm C, ∀ k, IsImageCpt Φ (tie k).A (tie (π k)).A := by
  intro E _ _ _ H D l Xo c O _ β Y S n C _ M tie hβ hinj hall Φ hΦ
  have hfin := c.fin
  have hopen := Y.jQ_open
  have hsurj := surjectiveOnStalks_spMap β hβ
  have hfst := isEmbedding_fst Y.s β
  have hlift : ∀ k, ∃ x : Sp (tie k).A.Ω₀ ⟶ Xo.XF c, x ≫ Y.j = (tie k).A.ξ₀ ∧
      spMap (tie k).A.fn ≫ x ≫ pullback.snd _ _ = spMap (tie k).A.cst ∧
      Function.Bijective (Scheme.stalkClosedPointTo x).hom := fun k => by
    have hover : spMap (tie k).A.fn ≫ (tie k).A.ξ₀ ≫ Y.s = spMap ((tie k).A.cst.comp β) := by
      have h1 : (tie k).A.ξ ≫ (tie k).A.f = spMap (tie k).A.fn ≫ (tie k).A.ξ₀ := (tie k).A.fn_over
      rw [← Category.assoc, ← h1, Category.assoc]
      exact (tie k).A.cst_over
    obtain ⟨x, h1, h2, h3⟩ := exists_lift Y.s Y.proj β hβ Y.jQ Y.jQ_dense (tie k).A.ξ₀ (tie k).A.gen₀
      (tie k).A.fn (tie k).A.cst hover
    rw [Y.jQ_over] at h2
    exact ⟨x, h1, h2, h3⟩
  choose x hx hcs hb using hlift
  obtain ⟨r, hr1, hr2⟩ : ∃ r : Xo.XF c ≅ Xo.XF c, r.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Φ.hom ∧
      r.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
    have hΦ' : Φ.inv ≫ Xo.s = Xo.s := by rw [Iso.inv_comp_eq, hΦ]
    let a : Xo.XF c ⟶ Xo.XF c := pullback.lift (pullback.fst _ _ ≫ Φ.hom) (pullback.snd _ _) (by
      rw [Category.assoc, hΦ, pullback.condition])
    let b : Xo.XF c ⟶ Xo.XF c := pullback.lift (pullback.fst _ _ ≫ Φ.inv) (pullback.snd _ _) (by
      rw [Category.assoc, hΦ', pullback.condition])
    have a1 : a ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Φ.hom := pullback.lift_fst _ _ _
    have a2 : a ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have b1 : b ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Φ.inv := pullback.lift_fst _ _ _
    have b2 : b ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    refine ⟨⟨a, b, ?_, ?_⟩, a1, a2⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, b1, reassoc_of% a1, Φ.hom_inv_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, b2, a2, Category.id_comp]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, a1, reassoc_of% b1, Φ.inv_hom_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, a2, b2, Category.id_comp]
  have hjemb : IsEmbedding Y.j := by
    have h := hfst.comp Y.jQ.isOpenEmbedding.isEmbedding
    have e : (Y.j : Xo.XF c → Y.X) = pullback.fst Y.s (spMap β) ∘ Y.jQ := by
      funext t
      exact Scheme.Hom.comp_apply _ _ _
    rw [e]
    exact h
  have hpt : ∀ k, Y.j (genPt (x k)) = genPt (tie k).A.ξ₀ := fun k => by
    show Y.j ((x k) _) = (tie k).A.ξ₀ _
    rw [← hx k]
    exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨π, hπ⟩ := exists_perm Y.j hjemb (fun k => genPt (x k))
    (fun a b hab => hinj (by simpa only [hpt] using hab))
    (fun k q hq => by
      rw [hpt] at hq ⊢
      exact GlobalTheory.CompanionTheory.Ar.CptInh.nogen _ (tie k).A.gen₀ _ hq)
    (fun q hq => by
      obtain ⟨k, hk⟩ := hall q hq
      exact ⟨k, (hpt k).trans hk⟩) r
  refine ⟨π, fun k => ?_⟩
  have hsame : genPt (x k ≫ r.hom) = genPt (x (π k)) := by
    refine Eq.trans ?_ (hπ k).symm
    exact Scheme.Hom.comp_apply _ _ _
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_pts (x k ≫ r.hom) (x (π k)) hsame (bijective_comp_iso r.hom (x k) (hb k)) (hb (π k))
  unfold IsImageCpt
  refine ⟨x k, x (π k), ψ, (hx k).symm, (hx (π k)).symm, ?_, ?_, hcs k, hcs (π k)⟩
  · rw [reassoc_of% hψ, hr1]
  · rw [reassoc_of% hψ, hr2]

end GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt
