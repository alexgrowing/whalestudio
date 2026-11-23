import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed

theorem gs_zero {X Z : Scheme.{0}} (q : Z ⟶ X) (z : Z) (U : X.Opens) : gs q z U 0 = 0 := by
  unfold gs
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem cst_comp_eq_zero {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {r : R}
    (hr : φ r = 0) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R')) (z : Z) :
    cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z r = 0 := by
  have h : ((Spec.map (CommRingCat.ofHom φ)).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    have := congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [hr, map_zero] at this
    exact this.symm
  rw [cst, ← gs_pull q _ z ⊤ trivial, h, gs_zero]

theorem app_comp_eq_zero {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U)) (t : Γ(Y, a ⁻¹ᵁ U))
    (h : (a.app U).hom f = resTop _ (scal (a ≫ p) r) * t) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have h' : (a.app U).hom f = constFn (a ≫ p) _ r * t := h
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, ← gs_pull b a z U hz, h', gs_mul _ _ _ hz',
    gs_constFn _ _ _ _ hz', hr, zero_mul, gs_zero]

theorem constFn_dvd_of_mem_ker {R : Type} [CommRing R] {X Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (r : R) (i : Z ⟶ X)
    (l : pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) ⟶ Z)
    (hl : l ≫ i = pullback.fst _ _) {W : X.Opens} (hW : IsAffineOpen W) {a : Γ(X, W)}
    (ha : a ∈ i.ker.ideal ⟨W, hW⟩) : constFn p W r ∣ a := by
  let φ : CommRingCat.of R ⟶ Γ(X, W) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W le_top
  have hφ : Spec.map φ = hW.fromSpec ≫ p := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hW le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, Spec.map_comp]
  have := ker_ideal_le_ker i hW
    (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom)))
    (pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom))) ≫
      hW.fromSpec)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((Ideal.span {r}).map φ.hom) φ.hom
        Ideal.le_comap_map)))
      (by
        rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
        rfl) ≫ l)
    (by rw [Category.assoc, hl, pullback.lift_fst]) ha
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at this
  exact this

theorem map_le_jacobson {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) :
    I.map φ ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_jacobson_of_surjective hφ]
  exact hI.trans (Ideal.jacobson_mono bot_le)

end ThickeningDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData ThickeningDetermines
  ThickeningDivisible in

theorem sec_div_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ n : ℕ, ∃ t : ∀ j, Γ((thickObj R I n H).left, (fstG I n H).left ⁻¹ᵁ N.U j), ∀ j, ((fstG I n H).left.app _).hom (s.f j) = resTop (Y := (thickObj R I n H).left) _ (scal ((fstG I n H).left ≫ H.hom) r) * t j) → ∃ s' : LB.Sec N, ∀ j, s.f j = resTop _ (scal H.hom r) * s'.f j := by
  intro R _ _ _ I hI H _ _ _ N hN s r hr hs
  let φ : R →+* R ⧸ Ideal.span {r} := Ideal.Quotient.mk _
  let q := Spec.map (CommRingCat.ofHom φ)
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback q).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom q
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom q))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom q))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have key := isIso_of_isClosedImmersion_of_thickenings _ (I.map φ)
    (map_le_jacobson φ Ideal.Quotient.mk_surjective hI) H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.snd (secIdeal hN s).subschemeι π) fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom q))
      have hπ : π ≫ H.hom = H₀.hom ≫ q := pullback.condition
      let b : (thickObj _ (I.map φ) n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG (I.map φ) n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))))
          (by
            rw [Category.assoc, hπ, Category.assoc, ← Spec.map_comp, ← Category.assoc]
            erw [pullback.condition]
            rw [Category.assoc, ← Spec.map_comp]
            rfl)
      have hb : b ≫ (fstG I n H).left = (fstG (I.map φ) n H₀).left ≫ π := pullback.lift_fst _ _ _
      obtain ⟨t, ht⟩ := hs n
      have h0 : ∀ j, (((fstG (I.map φ) n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j ↦ by
        rw [← hb]
        refine app_comp_eq_zero H.hom _ b r (fun z ↦ ?_) _ _ _ (ht j)
        rw [← Category.assoc, hb, Category.assoc, hπ, ← Category.assoc]
        exact cst_comp_eq_zero φ
          (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r)) _ z
      exact ⟨pullback.lift (IsClosedImmersion.lift _ ((fstG (I.map φ) n H₀).left ≫ π) (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0)) _ (IsClosedImmersion.lift_fac _ _ _),
        pullback.lift_snd _ _ _⟩
  refine exists_div_sec H.hom hr s fun j x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  have h1 := constFn_dvd_of_mem_ker H.hom r (secIdeal hN s).subschemeι
    (inv (pullback.snd (secIdeal hN s).subschemeι π) ≫ pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]) W.2
    (a := resG _ hW (s.f j)) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW).ge
        (Ideal.mem_span_singleton_self _))
  obtain ⟨c, hc⟩ := h1
  refine ⟨gs (𝟙 _) x W.1 c, ?_⟩
  have h2 := congrArg (gs (𝟙 _) x W.1) hc
  rw [gs_mul _ _ _ hxW, gs_constFn _ _ _ _ hxW, Category.id_comp] at h2
  exact (gs_res _ x hW hxW _).symm.trans h2

end GlobalTheory
