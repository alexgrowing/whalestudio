import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelAlg
import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelGeo
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

set_option backward.isDefEq.respectTransparency false

namespace PositivityTheory.HtPt.Gh

open GlobalTheory.CompanionTheory.Ar.LieTangent

section Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem htDual_le_lat {p : ℕ} (hpS : p ∈ S) (s : CMType H ⊕ CMType H) (q q' : Cpt 𝔐.ξ) (hqq : q'.1 ⤳ q.1)
    (hq : InFibre 𝔐.ξ p q) (hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p) (hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' q')
    (hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ q) (e : 𝔐.Li)
    (he : e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q) : e ∈ 𝔐.M.lat q' := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s q trivial
  have h1 := (hb q trivial hU).2
  have h2 := (hb q' trivial (hqq.mem_open U.isOpen hU)).2
  rw [Lat.patch_of_unique _ _ _ hpS hq hu] at h1
  rw [Lat.patch_of_not _ _ _ hq'] at h2
  have h3 : e ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range b) := by
    rw [← h1]
    cases s with
    | inr τ => exact he
    | inl τ =>
      exact Submodule.subset_span ⟨𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he, fun d _ =>
        Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ q) he⟩
  clear he
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    have : x ∈ Submodule.span (regAt 𝔐.ξ q') (Set.range b) := Submodule.subset_span hx
    rw [← h2] at this
    exact this.1
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨_, t, rfl⟩ := a
    exact Submodule.smul_mem _ (⟨genMap 𝔐.ξ q t, _, genMap_specializes q q'.2 hqq t⟩ : regAt 𝔐.ξ q') hx

end Reg

set_option maxHeartbeats 1000000 in
theorem hodge_tate_free_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS κ hfree hsand C _ _ v O' _ _ _ hv hvp z EC _ _ _ _ MC
    ρC s σ κz hact hσ hκ
  have hξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) := 𝔐.all _
  have hsp := centre_specializes (algebraMap O' C) z
  have hpu : ¬ IsUnit (p : O') := fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hvp.ne this
  have hq : InFibre 𝔐.ξ p ⟨centre z, h⟩ := fun hu => hpu ((unitAt_centre_iff hξ z h p).1 hu)
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, h⟩ → p' = p := by
    intro p' hp' hf
    by_contra hne
    have hc : IsCoprime (p' : O') (p : O') :=
      Nat.Coprime.cast ((Nat.coprime_primes (𝔐.S_prime p' hp') hp.out).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
    · exact hf ((unitAt_centre_iff hξ z h p').2 (isUnit_of_mul_isUnit_right h1))
    · exact hpu (isUnit_of_mul_isUnit_right h1)
  have hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' ⟨_, h'⟩ := fun p' hp' hf =>
    hf ((unitAt_centre_iff hξ _ h' p').2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (𝔐.S_prime p' hp').ne_zero)))
  have hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, h⟩ := fun a => by
    obtain ⟨_, t, ht, -⟩ := hσ a
    exact ⟨t, ht⟩
  obtain ⟨n, βb, gm, hβ, hVal⟩ := exists_frame 𝔐.M z MC h h'
  haveI : FiniteDimensional Ω 𝔐.Li := Module.Finite.of_basis βb
  obtain ⟨U, hU, b, hbs, hb⟩ := hfree.2 s ⟨centre z, h⟩ hq
  obtain ⟨hli, hbq⟩ := hb _ hq hU
  obtain ⟨f, hf1, hf2⟩ := exists_predual b hli hbs
  have hw : ∀ j, ∃ w ∈ omP 𝔐 p ⟨centre z, h⟩, (𝔐.Vgen s).dualRestrict w = b j := fun j => by
    have : b j ∈ ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict) ⟨centre z, h⟩ := by
      rw [hbq]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose w hw1 hw2 using hw
  have hw3 : ∀ j (e : 𝔐.Vgen s), w j e = b j e := fun j e => by rw [← hw2]; rfl
  have hgk : ∀ a, genMap 𝔐.ξ ⟨_, h'⟩ ((𝔐.X.presheaf.stalkSpecializes hsp).hom a) = genMap 𝔐.ξ ⟨centre z, h⟩ a :=
    fun a => genMap_specializes ⟨centre z, h⟩ h' hsp a
  have hfW : ∀ j, (f j : 𝔐.Li) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩ := fun j => by
    refine (𝔐.M.mem_htDual _ _ _ _ _ (f j)).2 fun u hu => ?_
    have hu' : u ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, h⟩) (Set.range b) := hbq ▸ hu
    clear hu
    induction hu' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine (hf1 i j).symm ▸ (?_ : (if i = j then (1 : Ω) else 0) ∈ regAt 𝔐.ξ ⟨centre z, h⟩)
      by_cases hij : i = j
      · rw [if_pos hij]; exact one_mem _
      · rw [if_neg hij]; exact zero_mem _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact mul_mem a.2 hx
  have hfib : ∀ L : Lat 𝔐.ξ 𝔐.Li, 𝔐.M.fibAt L z MC = Submodule.span O'
      {x | ∃ e ∈ (L ⟨centre z, h⟩ : Set 𝔐.Li),
        𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) e (MC.pt x)} := fun L => by
    unfold LieModel.fibAt
    congr 1
    ext x
    exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, h1, h2⟩, fun ⟨e, h1, h2⟩ => ⟨h, e, h1, h2⟩⟩
  rw [hfib, hfib]
  refine alg_main (A := 𝔐.X.presheaf.stalk (centre z)) (𝔐.X.presheaf.stalkSpecializes hsp).hom
    (genMap 𝔐.ξ ⟨_, h'⟩) (hξ.inj _) (Scheme.stalkClosedPointTo _).hom (Scheme.stalkClosedPointTo z).hom
    (fun a => congrArg (fun g => g.hom a) (stalk_base (algebraMap O' C) z)) βb gm _ hVal 𝔐.ρ ρC (𝔐.emb s) σ
    ?_ ?_ _ _ w (fun j => f j) hβ ?_ hfW ?_ ?_ ?_ κ κz ?_ ?_
  · intro a
    obtain ⟨_, t, h1, h2⟩ := hσ a
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro a e x hx
    haveI := 𝔐.t.act.hom a
    exact valAt_act 𝔐.M MC _ _ _ (𝔐.act a) (hact a) hx
  · intro j e he
    obtain ⟨t, ht⟩ := 𝔐.M.htOm_le _ _ _ (hw1 j) e he
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    obtain ⟨h1, h2⟩ := (𝔐.M.mem_htDual_iff _ _ _ _ _ e).1 he
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨t, ht⟩ := h2 _ (hw1 j)
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    have := congrArg Subtype.val (hf2 ⟨e, he⟩)
    simpa [← hw3] using this
  · intro j
    obtain ⟨u, hu'⟩ := (𝔐.M.exists_valAt_iff _ _).2
      ⟨h', htDual_le_lat 𝔐 hpS s ⟨centre z, h⟩ ⟨_, h'⟩ hsp hq hu hq' hreg _ (hfW j)⟩
    obtain ⟨x, rfl⟩ := MC.onto u hu'.isTanAt
    exact ⟨x, hu'⟩
  · obtain ⟨_, t, h1, h2⟩ := hκ
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro e he
    exact (((hsand _ hq).2.2.2 s).2 e he).1

end PositivityTheory.HtPt.Gh
