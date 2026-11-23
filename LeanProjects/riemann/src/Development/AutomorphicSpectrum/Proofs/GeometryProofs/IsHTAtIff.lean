import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUnique

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem isHTAt_iff (h455 : type_of% @GlobalTheory.T.lie_model_finite_base_change) (h876 : type_of% @GlobalTheory.T.section_eq_zero_of_values)
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (L : LB G.left) {n : ℕ} (hn : n ≠ 0)
    (hfull : FullTorsion G ξ n) {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω)
    (hx : Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (htor : Γ.IsTorsionAlong G x n i)
    {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E)
    (hj : ∀ v, (M.pt (j v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (κ.toRingHom.comp (algebraMap R (FractionRing R))))) ≫ (M₀.pt v).left)
    (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E)
    (hW : ∀ (t : T) (k : Type) [Field k] [IsAlgClosed k] (a : Ω →+* k) (xk gk : Over.mk (spMap a ≫ ξ) ⟶ G) (c : kˣ),
      xk.left = spMap a ≫ y.left → gk.left = spMap a ≫ ptG κ.toRingHom i t →
        (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = a (κ (algebraMap R _ (χ t : R)))))
    (hHT : Γ.IsHT i M₀ n χ w₀) (hwj : ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)))
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a : R, κ (algebraMap R _ a) ∈ regAt ξ q)
    (w' : Module.Dual Ω E) : M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum R, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ (κ.toRingHom.comp (algebraMap R (FractionRing R)))
    (κ.injective.comp (IsFractionRing.injective R _)) x hx p q hp hsub
  obtain ⟨s, hs, hv⟩ := hHT
  have hcore := fun W f hval (e' : E) (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (hv' : M.Extends q e' v) =>
    core_tan h455 M p.asIdeal.primeCompl Γ i x hzs (genMap ξ q) _ hg M₀ j hj n w₀ w hwj s hv W f hval e' v hv'.1 hv'.2
  obtain ⟨W₀, f₀, hW₀, hf₀⟩ := lift_sec G Γ x n i htor q.1 _ hzs s
  have hval₀ : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
      y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
        ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W₀, valAt (y ≫ i) W₀ h f₀ = valAt y ⊤ le_top s :=
    fun y b hb h => hf₀ y (Spec.map (CommRingCat.ofHom b)) (hb.trans (spec_comp _ _)) h
  have hlat := (lieLat_carrier X G Ω ξ E M q).1
  have hw : w ∈ M.omLat q := fun e' he' => by
    obtain ⟨v, hv'⟩ := (hlat e').1 he'
    obtain ⟨c, hc, -⟩ := hcore W₀ f₀ hval₀ e' v hv'
    exact ⟨c, hc.symm⟩
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · rintro ⟨-, W, f, hWm, hf, hd⟩
    have hsec : (i.app W).hom f - Γ.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s = 0 := by
      refine h876 R T Γ (i ⁻¹ᵁ W) _ fun t h => ?_
      rw [valAt_sub, sub_eq_zero]
      refine Eq.trans ?_ (valAt_res _ _ ⊤ le_top h le_top s).symm
      rw [hs t]
      refine (valAt_comp (Γ.pt t).left i W h f).symm.trans ?_
      let k := AlgebraicClosure Ω
      let a : Ω →+* k := algebraMap Ω k
      let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
      obtain ⟨g, hg1, hg2⟩ := tors_ex κ.toRingHom htor hx t
      let c : kˣ := Units.map ((a.comp κ.toRingHom).comp (algebraMap R (FractionRing R))).toMonoidHom (χ t)
      have e0 : (ψ ≫ g).left = spMap a ≫ ptG κ.toRingHom i t := by rw [← hg2]; rfl
      have e1 : (ψ ≫ g).left = Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i := by
        rw [e0, spec_comp, Category.assoc]
      have h1 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i) ⁻¹ᵁ W :=
        fun z _ => h (by trivial)
      have h2 := hf k a (ψ ≫ y) (ψ ≫ g) c (by rw [e1]; exact h1) rfl (by rw [← comp_pow', hg1, MonObj.comp_one])
        ((hW t k a (ψ ≫ y) (ψ ≫ g) c rfl e0).2 rfl)
      apply (a.comp κ.toRingHom).injective
      exact (valAt_spec (a.comp κ.toRingHom) _ W h h1 f).symm.trans ((valAt_congr e1 W _ h1 f).symm.trans h2)
    have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
        y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
          ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W, valAt (y ≫ i) W h f = valAt y ⊤ le_top s := by
      intro B _ y _ _ h
      refine (valAt_comp y i W h f).trans ?_
      rw [sub_eq_zero.1 hsec]
      exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
    refine ⟨(n : Ω)⁻¹ • (w' - w), fun e' he' => ?_, ?_⟩
    · obtain ⟨v, hv'⟩ := (hlat e').1 he'
      have hm : ⊤ ≤ v.left ⁻¹ᵁ W := HtUniq.tan_le v hv'.1 hWm
      obtain ⟨c, hc, hr⟩ := hcore W f hval e' v hv'
      obtain ⟨r, hr⟩ := hr hm
      obtain ⟨r', hr', he⟩ := hd e' v hv' hm
      have : ((n : Ω)⁻¹ • (w' - w)) e' = r' - genMap ξ q r := by
        have he' : w' e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * r' := he
        have hc' : w e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * genMap ξ q r := by
          rw [hc, hr, map_add, map_mul, map_natCast]
          rfl
        rw [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hn', mul_sub, he', hc',
          add_sub_add_left_eq_sub]
      rw [this]
      exact sub_mem hr' ⟨r, rfl⟩
    · rw [← Nat.cast_smul_eq_nsmul Ω, smul_smul, mul_inv_cancel₀ hn', one_smul, add_sub_cancel]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨add_mem hw (nsmul_mem hu n), W₀, f₀, hW₀, ?_, ?_⟩
    · intro K _ _ a xk g' c h hxk hg' hweil
      obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
      have hg0 : g₀ ^ n = 1 := pow_descend a hg₀ hg'
      obtain ⟨t, ht⟩ := tors_pt κ.toRingHom htor hx g₀ hg0
      have hc₁ := (hW t K a xk g' c hxk (by rw [hg₀, ht])).1 hweil
      have e1 : g'.left = (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left) ≫ i := by
        rw [hg₀, ht, spec_comp]; simp only [ptG, Category.assoc]
      refine (valAt_congr e1 W₀ h (by rw [← e1]; exact h) f₀).trans ?_
      rw [hval₀ _ (a.comp (genMap ξ q)) (by
        rw [Category.assoc, Over.w, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, spec_comp (algebraMap R _)]; rfl)]
      refine (valAt_spec (a.comp κ.toRingHom) (Γ.pt t).left ⊤ le_top le_top s).trans ?_
      rw [hs t, hc₁]
      rfl
    · intro e' v hv' h
      obtain ⟨c, hc', hr⟩ := hcore W₀ f₀ hval₀ e' v hv'
      obtain ⟨r, hr⟩ := hr h
      refine ⟨genMap ξ q r + u e', add_mem ⟨r, rfl⟩ (hu e' ((hlat e').2 ⟨v, hv'⟩)), ?_⟩
      rw [LinearMap.add_apply, LinearMap.smul_apply, hc', hr, map_add, map_mul, map_natCast, nsmul_eq_mul, mul_add,
        ← add_assoc]
      rfl

end GlobalTheory.CompanionTheory.HtLink
