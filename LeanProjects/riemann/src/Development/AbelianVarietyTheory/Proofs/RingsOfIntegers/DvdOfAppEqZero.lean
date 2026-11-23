import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GermDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThickeningDetermines

theorem dvd_of_app_eq_zero {R : Type} [CommRing R] (r : R) {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hf : ((pullback.fst p (spMap (Ideal.Quotient.mk (Ideal.span {r})))).app U).hom f = 0) :
    constFn p U r ∣ f := by
  have h := ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (Ideal.span {r})))) hU f hf
  have hk : RingHom.ker (spMap (Ideal.Quotient.mk (Ideal.span {r}))).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r} := by
    intro x hx
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    have e := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))))
    have h0 : Ideal.Quotient.mk (Ideal.span {r}) a = 0 :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {r}))).inv).1
        ((e.trans hx).trans (map_zero _).symm)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    exact Ideal.mem_span_singleton.2 (map_dvd (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h0)
  have h' := Ideal.map_mono hk h
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h'
  exact h'

theorem cst_zero {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem app_eq_zero_of_dvd {R : Type} [CommRing R] (r : R) {X Y Z : Scheme.{0}} (p : X ⟶ Sp R)
    (a : Y ⟶ X) (m : Z ⟶ Y) (t : Z ⟶ Sp (R ⧸ Ideal.span {r}))
    (ht : m ≫ a ≫ p = t ≫ spMap (Ideal.Quotient.mk (Ideal.span {r})))
    (U : X.Opens) (f : Γ(X, U)) (h : ∀ y : Y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) :
    ((m ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz => ?_
  have hz' : a (m z) ∈ U := hz
  have e1 : gs (𝟙 Z) z ((m ≫ a) ⁻¹ᵁ U) (((m ≫ a).app U).hom f) = gs (m ≫ a) z U f :=
    (gs_pull (𝟙 Z) (m ≫ a) z U hz f).trans (by rw [Category.id_comp])
  have e2 : gs (m ≫ a) z U f = (m.stalkMap z).hom (gs a (m z) U f) := by
    rw [← gs_pull m a z U hz', gs_stalkMap m z _ hz', gs_pull (𝟙 Y) a (m z) U hz', Category.id_comp]
  have e3 : (m.stalkMap z).hom (cst (a ≫ p) (m z) r) = 0 := by
    rw [H1.cst_stalkMap, ht, cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r), cst_zero]
  obtain ⟨c, hc⟩ := h _ hz'
  rw [e1, e2, hc, map_mul, e3, zero_mul, gs_eq (𝟙 Z) z _ hz, map_zero, map_zero]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ (n : ℕ) (x : (thickObj R I n H).left) (j : N.ι), (fstG I n H).left x ∈ N.U j → Geo.Tor.cst ((fstG I n H).left ≫ H.hom) x r ∣ Geo.Tor.gs (fstG I n H).left x (N.U j) (s.f j)) → ∃ s' : LB.Sec N, SecIsMul H.hom r s s' := by
  intro R _ _ _ I hI H _ _ _ N hN s r hr h
  let q := Ideal.Quotient.mk (Ideal.span {r})
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback (spMap q)).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom (spMap q)
  let I₀ := I.map q
  have hI₀ : I₀ ≤ Ideal.jacobson ⊥ := by
    refine Ideal.map_le_iff_le_comap.2 (hI.trans ?_)
    rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
    exact Ideal.jacobson_mono bot_le
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom (spMap q)))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom (spMap q)))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom (spMap q)))
  let κ := (secIdeal hN s).subschemeι
  have hiso := isIso_of_isClosedImmersion_of_thickenings _ I₀ hI₀ H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.fst π κ) fun n ↦ by
      have : IsClosedImmersion (thick _ I₀ n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I₀ n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ I₀ n)))
      let m : (thickObj _ I₀ n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG I₀ n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ I₀ n) ≫ spMap (Ideal.quotientMap (I₀ ^ (n + 1)) q
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))
          (by
            have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
            have e2 : (fstG I₀ n H₀).left ≫ H₀.hom =
              pullback.snd H₀.hom (thick _ I₀ n) ≫ thick _ I₀ n := pullback.condition
            rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
              ← Spec.map_comp, ← Spec.map_comp]
            rfl)
      have hm : m ≫ (fstG I n H).left = (fstG I₀ n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG I₀ n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j => by
        rw [← hm]
        refine app_eq_zero_of_dvd r H.hom _ m ((fstG I₀ n H₀).left ≫ H₀.hom) ?_ _ _
          fun y hy => h n y j hy
        have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
        rw [← Category.assoc, hm, Category.assoc, Category.assoc, e1]
      have hle : κ.ker ≤ ((fstG I₀ n H₀).left ≫ π).ker := by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0
      exact ⟨pullback.lift (fstG I₀ n H₀).left (IsClosedImmersion.lift κ _ hle)
        (IsClosedImmersion.lift_fac _ _ _).symm, pullback.lift_fst _ _ _⟩
  have hker : secIdeal hN s ≤ π.ker := by
    have e : π = (inv (pullback.fst π κ) ≫ pullback.snd π κ) ≫ κ := by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [e]
    exact (Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)).ge.trans
      (Scheme.Hom.le_ker_comp _ _)
  refine exists_div_sec H.hom hr s fun j x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    H.left.isBasis_affineOpens.exists_subset_of_mem_open hx (N.U j).isOpen
  have hle : U ≤ N.U j := hUW
  have h1 := EffCartierData.ideal_locIdeal _ _ (exists_mem_chart hN)
    (associated_germ_sec s) ⟨U, hU⟩ j hle
  have h2 := Scheme.Hom.ideal_ker_le π ⟨U, hU⟩
    (hker ⟨U, hU⟩ (h1.ge (Ideal.mem_span_singleton_self _)))
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero r H.hom hU
    ((H.left.presheaf.map (homOfLE hle).op).hom (s.f j)) h2
  have hxU' : (𝟙 H.left : H.left ⟶ H.left) x ∈ U := hxU
  refine ⟨gs (𝟙 H.left) x U g, ?_⟩
  rw [← gs_res (𝟙 H.left) x hle hxU' (s.f j), hg, gs_mul _ x U hxU',
    gs_constFn H.hom U _ x hxU', Category.id_comp]

end GlobalTheory.GermDiv
