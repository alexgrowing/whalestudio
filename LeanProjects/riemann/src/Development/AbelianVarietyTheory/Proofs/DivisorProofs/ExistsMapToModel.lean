import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.RecSpan

open GlobalTheory.HTLat.OmegaRank

theorem exists_eigenbasis {V O : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing O]
    [Algebra V O] [Module.Flat V O] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {Λ : Type} (act : Λ → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : Λ → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w)
    {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (spMap (algebraMap V O)) π)
    (act' : Λ → (G' ⟶ G')) (ha : ∀ a, (act' a).left ≫ π = π ≫ (act a).left) :
    ∃ u' : Fin m → (specO O (DualNumber O) ⟶ G'),
      (∀ i, (u' i).left ≫ π = spMap (dualMap (algebraMap V O)) ≫ (u i).left) ∧
      ∀ w : LieG G', (∀ a, w.1 ≫ act' a = ptMap (dualScale (algebraMap V O (χ a))) ≫ w.1) →
        ∃ c : Fin m → O, w.1 = (List.ofFn fun i => ptMap (dualScale (c i)) ≫ u' i).prod := by
  obtain ⟨u', -, -, h3, h4⟩ := PlaceInt.Ext.exists_eigenbasis_pullback (V' := O) G act χ u ht he hb
  obtain ⟨e, he, he'⟩ := grpPullback_iso hπ (isGrpPullback_pullback G _)
  refine ⟨fun i => u' i ≫ e.inv, fun i => ?_, fun w hw => ?_⟩
  · rw [← he', ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact h4 i
  · have hc : ∀ a, e.hom ≫ (Over.pullback (spMap (algebraMap V O))).map (act a) = act' a ≫ e.hom := fun a => by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      have A : ((Over.pullback (spMap (algebraMap V O))).map (act a)).left ≫ pullback.fst G.hom _ =
        pullback.fst G.hom _ ≫ (act a).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, A, he', ha, ← Category.assoc, he']
    obtain ⟨c, ⟨y, hy, hy'⟩, -⟩ := h3 (w.1 ≫ e.hom) (by
      have h := congrArg (fun z => (z ≫ e.hom).left) w.2
      simp only [Category.assoc, IsMonHom.one_hom] at h
      exact h) fun a => by
        have h := congrArg (fun z => (z ≫ e.hom).left) (hw a)
        simp only [Category.assoc, ← hc] at h
        exact h
    refine ⟨c, ?_⟩
    have h := congrArg (IsMonHom.monoidHom e.inv _) hy'
    rw [map_list_prod, List.map_ofFn] at h
    refine Eq.trans ?_ (h.trans ?_)
    · exact ((Category.assoc _ _ _).trans (by rw [e.hom_inv_id, Category.comp_id])).symm
    · congr 2
      funext i
      exact (congrArg (· ≫ e.inv) (show y i = ptMap (dualScale (c i)) ≫ u' i from Over.OverMorphism.ext (hy i))).trans
        (Category.assoc _ _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [StarRing (𝓞 E)] {P : Point p v O (𝓞 E)}

theorem exists_map_to_model {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {x₀ : Sp F ⟶ Xo.X} {k : F →+* C} {kO : V →+* O} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    (h : PointOver P x₀ k kO ψ) {G : SAB H (Sp V)} {t : SAB H (Sp F)} (n₁ : SABMap t Xo.univ.t x₀)
    (n₂ : SABMap t G (spMap (algebraMap V F))) :
    ∃ (π : P.G.left ⟶ G.G.left) (φ : P.A.A.left ⟶ t.G.left), IsGrpPullback P.G G.G (spMap kO) π ∧
      (∀ a, (P.oG.act a).left ≫ π = π ≫ (G.act.act a).left) ∧ φ ≫ t.G.hom = P.A.A.hom ≫ spMap k ∧
      φ ≫ n₂.φ = P.gen ≫ π ∧ φ ≫ n₁.φ = ψ := by
  obtain ⟨-, G', t', m₁, m₂, π, φ, h1, h2, h3, h4, rfl, -⟩ := h
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨e, he, he'⟩ := LocModelLie.exists_iso_of_models HomExtExamples.homExtSt_holds V F G'.G G.G G'.semi G.semi t'.G
    m₂.cart (((isGrpPullback_of_iso a).comp n₂.cart).congr (Category.id_comp _) rfl)
  have c₁ : ∀ b, (t'.act.act b).left ≫ a.hom.left = a.hom.left ≫ (t.act.act b).left := fun b =>
    n₁.cart.1.hom_ext (by rw [Category.assoc, Category.assoc, n₁.act, ha', m₁.act, ← Category.assoc, ha'])
      (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w])
  have c₂ : ∀ b, (G'.act.act b).left ≫ e.hom.left = e.hom.left ≫ (G.act.act b).left := fun b => by
    haveI := G.semi.separated
    haveI := G'.semi.smooth
    haveI : IsSchemeTheoreticallyDominant (spMap (algebraMap V F)) :=
      schDom_spec_map _ (IsFractionRing.injective V F)
    haveI : IsSchemeTheoreticallyDominant m₂.φ := .of_isPullback m₂.cart.1.flip
    refine ext_of_schDom G.G.hom (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w]) m₂.φ ?_
    rw [← Category.assoc, ← m₂.act, Category.assoc, he', ← Category.assoc, c₁, ← Category.assoc m₂.φ, he',
      Category.assoc, Category.assoc, n₂.act]
  refine ⟨π ≫ e.hom.left, φ ≫ a.hom.left, (h1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl,
    fun b => ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h2, Category.assoc, Category.assoc, c₂]
  · rw [Category.assoc, Over.w, h3.1.w]
  · rw [Category.assoc, ← he', ← Category.assoc, h4, Category.assoc]
  · rw [Category.assoc, ha']

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    (dualMap f).comp (dualMap g) = dualMap (f.comp g) := by
  ext s <;> simp [dualMap]

theorem dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem ext_generic {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : spMap (dualMap (algebraMap O C)) ≫ y.left = spMap (dualMap (algebraMap O C)) ≫ y'.left) : y = y' := by
  haveI : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  haveI := P.semi.separated
  exact Over.OverMorphism.ext (ext_of_schDom P.G.hom ((Over.w y).trans (Over.w y').symm) _ h)

theorem span_bLie_eq_wRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embInt c P.integers τ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨x j, (hx j).isEig hP (z.eig τ j)⟩, rfl⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨G, t, n₁, n₂, ⟨ub, u₁, u₂, u₃, u₄⟩, -⟩ := y₀.2.2
  obtain ⟨π, φ, h1, h2, h3, h4, h5⟩ := exists_map_to_model hP n₁ n₂
  letI := kO.toAlgebra
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have inj : Function.Injective (algebraMap T.V O) := fun a b h => IsFractionRing.injective T.V T.Fr
    (k.toRingHom.injective ((hP.1 a).symm.trans ((congrArg _ h).trans (hP.1 b))))
  haveI : FaithfulSMul T.V O := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  haveI : Module.Flat T.V O := inferInstance
  haveI := G.semi.smooth
  haveI := G.act.hom
  choose χ hχ using fun a => int_val c T io τ a
  have hχ' : ∀ a, algebraMap T.V O (χ a) = embInt c P.integers τ a := fun a => P.integers.hom_inj (by
    rw [algebraMap_embInt, ← k.commutes]
    exact (hP.1 _).trans (congrArg k (hχ a)))
  obtain ⟨u', v₁, v₂⟩ := exists_eigenbasis G.G G.act.act χ (ub τ) (u₁ τ) (fun i a => u₂ τ i a _ (hχ a))
    (fun w hw he => u₃ τ w hw fun a z hz => by
      obtain rfl : z = χ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ a).symm)
      exact he a) h1 P.oG.act h2
  have hc : ∀ j, Corr P (x j).1 (u' j) := fun j => by
    obtain ⟨xG, s, s₁, s₂, s₃⟩ := hx j
    obtain ⟨r, r₁, r₂⟩ := u₄ τ j
    have r₃ : r ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
      have : Mono (spMap (algebraMap T.V T.Fr)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
      refine (cancel_mono (spMap (algebraMap T.V T.Fr))).1 ?_
      have k : (ub τ j).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ j)
      rw [Category.assoc, ← n₂.cart.1.w, ← Category.assoc, r₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k).trans (dualMap_alg _))
    have e₁ : s.left ≫ φ = spMap (dualMap k.toRingHom) ≫ r := n₁.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, r₁, h5, s₂, hz.2.1])
      (by rw [Category.assoc, Category.assoc, r₃, h3, dualMap_alg, ← Category.assoc, Over.w s]; rfl)
    have e₂ : xG.1 = u' j := ext_generic (h1.1.hom_ext ?_ (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w]))
    · exact e₂ ▸ s₁
    have e₃ : k.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap O C).comp (algebraMap T.V O) :=
      RingHom.ext fun a => (hP.1 a).symm
    rw [← s₃, Category.assoc, ← h4, ← Category.assoc, e₁, Category.assoc, r₂, Category.assoc, v₁, ← Category.assoc,
      ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_comp, dualMap_comp, e₃]
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hl := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p)
  have hr := existsUnique_right (P := P) hp (isAdicComplete_dualNumber p)
  obtain ⟨y, hy, -⟩ := hr w.1
  have y₁ := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [w.2] at y₁
  obtain ⟨a, ha⟩ := v₂ ⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique y₁ Corr.one⟩ fun a =>
    (hr _).unique (corr_act hy a) (by
      rw [hχ', show w.1 ≫ P.oGt.act a = _ from congrArg Subtype.val (hw a)]
      exact hy.comp _)
  let S : Submonoid (specO O (DualNumber O) ⟶ P.G) :=
    { carrier := {y | ∃ w : LieG P.Gt, Corr P w.1 y ∧ P.bLie w ∈ Submodule.span O (Set.range fun j => P.bLie (x j))}
      mul_mem' := by
        rintro _ _ ⟨a, a₁, a₂⟩ ⟨b, b₁, b₂⟩
        exact ⟨lieAdd a b, a₁.mul b₁, P.bLie_add a b ▸ Submodule.add_mem _ a₂ b₂⟩
      one_mem' := ⟨lieZero P.Gt, Corr.one, P.bLie_zero ▸ Submodule.zero_mem _⟩ }
  obtain ⟨w', w₁, w₂⟩ : y ∈ S := by
    rw [show y = _ from ha]
    refine S.list_prod_mem fun s hs => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hs
    exact ⟨AvDefs.lieScale P.Gt (a j) (x j), (hc j).comp _,
      P.bLie_scale (a j) (x j) ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
  obtain rfl : w = w' := Subtype.ext ((hl y).unique hy w₁)
  exact w₂

end GlobalTheory.CompHt.RecSpan
