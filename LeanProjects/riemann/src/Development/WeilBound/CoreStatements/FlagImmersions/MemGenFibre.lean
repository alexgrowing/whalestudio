import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparison
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr (spec_dual_comp spec_dual_comp' frame_change coeff_of_span)

noncomputable section

namespace RootFieldNumerics.RF

namespace FV

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [Field L]
  {z : Spec (CommRingCat.of L) ⟶ X}

theorem mul {a b : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem isUnit (x : X.presheaf.stalk (centre z)) (h : (Scheme.stalkClosedPointTo z).hom x ≠ 0) : IsUnit x :=
  (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ h)

theorem inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x := isUnit x hr
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem unique {a : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z a s) : r = s := by
  obtain ⟨h, x, hx, rfl⟩ := h
  obtain ⟨_, y, hy, rfl⟩ := h'
  by_contra hne
  have hu : IsUnit (x - y) := isUnit _ fun h0 =>
    hne (sub_eq_zero.1 ((map_sub (Scheme.stalkClosedPointTo z).hom x y).symm.trans h0))
  have := hu.map (genMap ξ ⟨centre z, h⟩)
  rw [map_sub, hx, hy, sub_self] at this
  exact not_isUnit_zero this

end FV

namespace VP

variable {L : Type} [Field L]

theorem val_of_comb {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {z : Spec (CommRingCat.of L) ⟶ X}
    (hc : genPt ξ ⤳ centre z) {n : ℕ} (b : Fin n → E) (vb : Fin n → (epsAt z ⟶ G)) (hb : ∀ k, M.ValAt z (b k) (vb k))
    (t : Fin n → X.presheaf.stalk (centre z)) :
    ∃ w, M.ValAt z (∑ k, genMap ξ ⟨centre z, hc⟩ (t k) • b k) w ∧
      IsComb (fun k => (Scheme.stalkClosedPointTo z).hom (t k)) vb w := by
  let u : Fin n → (epsAt z ⟶ G) := fun k => LieTangent.epsScale z ((Scheme.stalkClosedPointTo z).hom (t k)) ≫ vb k
  have hu : ∀ k, M.ValAt z (genMap ξ ⟨centre z, hc⟩ (t k) • b k) (u k) := fun k => (hb k).smul hc (t k)
  have key : ∀ (m : ℕ) (x : Fin m → E) (w : Fin m → (epsAt z ⟶ G)), (∀ k, M.ValAt z (x k) (w k)) →
      M.ValAt z (∑ k, x k) (List.ofFn w).prod := by
    intro m
    induction m with
    | zero => intro x w _; simpa using LieModel.valAt_zero M hc
    | succ m ih =>
      intro x w h
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (h 0).add (ih _ _ fun k => h k.succ)
  exact ⟨_, key n _ u hu, u, fun k => rfl, rfl⟩

theorem tie_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    {Z : CptOver Y U} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li} (ht : CptIn.IsTie Z 𝔐 i j)
    {z : Spec (CommRingCat.of L) ⟶ 𝔐.X} {x : Spec (CommRingCat.of L) ⟶ Y.X} (hx : x = z ≫ 𝔐.f) {e : Z.V}
    {v' : epsAt x ⟶ Y.t.G} {w : epsAt z ⟶ 𝔐.t.G} (h1 : Z.M.ValAt x e v') (h2 : 𝔐.M.ValAt z (j e) w) :
    w.left ≫ 𝔐.m.φ = v'.left := by
  subst hx
  obtain ⟨hc1, vx₀, hvx₀, e1₀⟩ := h1
  obtain ⟨hc2, ve, hve, e2⟩ := h2
  have hD : Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i := ht.1
  have hcart := 𝔐.m.cart
  have hc1' : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z) := hc1
  let vx : epsAt (Y.X.fromSpecStalk (𝔐.f (centre z))) ⟶ Y.t.G := vx₀
  have hvx : Z.M.Extends ⟨𝔐.f (centre z), hc1'⟩ e vx := hvx₀
  have e5 : ((Scheme.stalkClosedPointTo (z ≫ 𝔐.f)).hom : Y.X.presheaf.stalk (𝔐.f (centre z)) →+* L) =
      (Scheme.stalkClosedPointTo z).hom.comp (𝔐.f.stalkMap (centre z)).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp z 𝔐.f)
  have e1 : v'.left = Spec.map (CommRingCat.ofHom (dualMap
      ((Scheme.stalkClosedPointTo z).hom.comp (𝔐.f.stalkMap (centre z)).hom))) ≫ vx.left := by
    refine e1₀.trans ?_
    exact congrArg (fun g : Y.X.presheaf.stalk (𝔐.f (centre z)) →+* L =>
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ vx.left) e5
  have hst : Spec.map (CommRingCat.ofHom (𝔐.f.stalkMap (centre z)).hom) ≫ Y.X.fromSpecStalk (𝔐.f (centre z)) =
      𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f := by
    simpa using Scheme.Hom.SpecMap_stalkMap_fromSpecStalk 𝔐.f (x := centre z)
  let A : epsAt (𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f) ⟶ Y.t.G := Over.homMk (ve.left ≫ 𝔐.m.φ) (by
    have h0 := Over.w ve
    change (ve.left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = Spec.map _ ≫ 𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ve.left ≫ ·) hcart.1.w).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ 𝔐.f) h0).trans ?_
    exact Category.assoc _ _ _)
  let B : epsAt (𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f) ⟶ Y.t.G :=
    LieTangent.epsBase (𝔐.f.stalkMap (centre z)).hom hst ≫ vx
  have hA : IsTanAt Y.t.G _ A := by
    have h1 : _ ≫ ve.left = (1 : Over.mk (𝔐.X.fromSpecStalk (centre z)) ⟶ 𝔐.t.G).left := hve.1
    have h2 := congrArg (fun q => q.left) (map_one (pushHom hcart (Over.mk (𝔐.X.fromSpecStalk (centre z)))))
    change Spec.map _ ≫ ve.left ≫ 𝔐.m.φ = _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔐.m.φ) h1).trans h2)
  have hB : IsTanAt Y.t.G _ B := LieTangent.isTanAt_base _ hst hvx.1
  have hAB : A = B := by
    refine LieTangent.tan_ext (𝔐.tie.gen.inj ⟨centre z, hc2⟩) hA hB ?_
    change _ ≫ ve.left ≫ 𝔐.m.φ = _ ≫ Spec.map _ ≫ vx.left
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ 𝔐.m.φ) hve.2.symm).trans ?_
    refine (ht.2.2.2 e).trans ?_
    refine (congrArg (_ ≫ ·) hvx.2).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ vx.left) (spec_dual_comp i (genMap (Z.ξ₀ ≫ Y.j) ⟨𝔐.f (centre z), hc1'⟩)
      (genMap 𝔐.ξ ⟨centre z, hc2⟩) (𝔐.f.stalkMap (centre z)).hom
      fun s => (PullReg.stalkMap_comp_genMap hD ⟨centre z, hc2⟩ hc1' s).symm)
  have hAB' : ve.left ≫ 𝔐.m.φ = Spec.map (CommRingCat.ofHom (dualMap (𝔐.f.stalkMap (centre z)).hom)) ≫ vx.left :=
    congrArg (fun q => q.left) hAB
  refine (congrArg (· ≫ 𝔐.m.φ) e2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hAB').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ e1.symm
  refine congrArg (· ≫ vx.left) ?_
  exact spec_dual_comp' _ _

theorem val_const' {X : Scheme.{0}} {Ω : Type} [Field Ω] {O : Type} [CommRing O] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (g : X ⟶ Sp O) {σ₀ : O →+* Ω} (hs : ξ ≫ g = spMap σ₀) {σ : O →+* L} (z : Spec (CommRingCat.of L) ⟶ X)
    (hz : z ≫ g = spMap σ) (h : genPt ξ ⤳ centre z) (c : O) : ValAt ξ z (σ₀ c) (σ c) := by
  refine ⟨h, GagaRat.cst g (centre z) c, ?_, ?_⟩
  · have hg : genPt (ξ ≫ g) ⤳ g (centre z) := h.map g.continuous
    rw [GagaRat.cst, GagaRat.genMap_stalkMap' ξ g ⟨centre z, h⟩ hg]
    have e : ((Sp O).presheaf.stalkSpecializes hg).hom (GagaRat.cgerm (g (centre z)) c) =
        GagaRat.cgerm (genPt (ξ ≫ g)) c :=
      congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom c))
        (TopCat.Presheaf.germ_stalkSpecializes (Sp O).presheaf (U := ⊤) trivial hg)
    show (Scheme.stalkClosedPointTo (ξ ≫ g)).hom (((Sp O).presheaf.stalkSpecializes hg).hom (GagaRat.cgerm (g (centre z)) c)) = _
    rw [e]
    exact GagaRat.closedPointTo_cgerm (ξ ≫ g) σ₀ hs c
  · have e := congrArg (fun t => t.hom (GagaRat.cgerm (g (centre z)) c)) (Scheme.stalkClosedPointTo_comp z g)
    exact e.symm.trans (GagaRat.closedPointTo_cgerm (z ≫ g) σ hz c)

theorem exists_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (s : c.F →+* L) (z : Spec (CommRingCat.of L) ⟶ 𝔐.X), genPt 𝔐.ξ ⤳ centre z → CptIn.IsTie Z 𝔐 i j → 𝔐.Interior z → (∀ a : c.F, ValAt 𝔐.ξ z (𝔐.cst a) (s a)) → ∃ y₀ : Sp L ⟶ Xo.XF c, z ≫ 𝔐.f = y₀ ≫ Y.j ∧ Set.range y₀ ⊆ U ∧ y₀ ≫ pullback.snd _ _ = spMap s ∧ ∃ h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y₀ ≫ Y.j), (⟨_, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := by

  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J y 𝔐 i j s z hc ht hint hcst
  have hD : Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i := ht.1
  have hz₀ : z ≫ 𝔐.f ≫ Y.s = spMap (s.comp (algebraMap (𝓞 c.F) c.F)) := by
    have hp : z ≫ 𝔐.f ≫ Y.s = spMap (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom := by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hv := val_const' (𝔐.f ≫ Y.s) 𝔐.cst_over z hp hc
    have e : (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom = s.comp (algebraMap (𝓞 c.F) c.F) :=
      RingHom.ext fun a => FV.unique (hv a) (hcst _)
    rw [hp, e]
  have hsq : (z ≫ 𝔐.f) ≫ Y.s = spMap s ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hz₀]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let w := pullback.lift (z ≫ 𝔐.f) (spMap s) hsq
  have hw1 : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw2 : w ≫ pullback.snd _ _ = spMap s := pullback.lift_snd _ _ _
  have hab : 𝔐.f (centre z) ∈ abLocus Y.t.G := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)).2 hint
  have hrange : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen]
    have hp : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst hp
    have e : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w (IsLocalRing.closedPoint L)) = 𝔐.f (centre z) :=
      congrArg (fun t : Spec (CommRingCat.of L) ⟶ Y.X => t (IsLocalRing.closedPoint L)) hw1
    show _ ∈ abLocus Y.t.G
    rw [e]
    exact hab
  haveI := Y.jQ_open
  let y₀ : Sp L ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hrange
  have hy : y₀ ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  have hj : y₀ ≫ Y.j = z ≫ 𝔐.f := by
    show y₀ ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hy, hw1]
  have hs : y₀ ≫ pullback.snd _ _ = spMap s := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hw2]
  have hcen : centre (y₀ ≫ Y.j) = 𝔐.f (centre z) := by rw [hj]; rfl
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y₀ ≫ Y.j) := by
    rw [hcen, ← hD.map_genPt]
    exact hc.map 𝔐.f.continuous
  refine ⟨y₀, hj.symm, ?_, hs, h, ?_⟩
  · rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst hp
    refine (Z.closure _).2 ?_
    haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
    haveI : IsPreimmersion Y.j := by
      show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
      infer_instance
    have hind : Topology.IsInducing Y.j := Y.j.isEmbedding.isInducing
    exact hind.specializes_iff.1 h
  · exact ⟨Y.jQ (y₀ (IsLocalRing.closedPoint L)), rfl⟩

theorem val_pull₀ {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (z : Spec (CommRingCat.of L) ⟶ X') (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : L}
    (hv : ValAt ξ (z ≫ f) a r) : ValAt ξ' z (i a) r := by
  obtain ⟨h, s, rfl, rfl⟩ := hv
  exact ⟨h', (f.stalkMap (centre z)).hom s, PullReg.stalkMap_comp_genMap hD ⟨centre z, h'⟩ h s,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z f)).symm⟩

theorem mem_genFibre [CharZero L] {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of L) ⟶ X) (hc : genPt ξ ⤳ centre z) : (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have hx : (Scheme.stalkClosedPointTo z).hom (o : X.presheaf.stalk (centre z)) ≠ 0 := by
    intro h0
    have e := (map_intCast (Scheme.stalkClosedPointTo z).hom o).symm.trans h0
    exact ho (by exact_mod_cast e)
  obtain ⟨x, hxo⟩ := FV.isUnit _ hx
  have e : genMap ξ ⟨centre z, hc⟩ x.val = algebraMap ℤ Ω o := by rw [hxo, map_intCast]; simp
  have hu : IsUnit (algebraMap ℤ Ω o) := e ▸ (x.isUnit.map (genMap ξ ⟨centre z, hc⟩))
  refine ⟨hu.ne_zero, ⟨x.val, e⟩, ⟨x⁻¹.val, ?_⟩⟩
  rw [← e, ← map_units_inv]

theorem comb_push {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {z : Spec (CommRingCat.of L) ⟶ X'}
    {x : Spec (CommRingCat.of L) ⟶ X} (hx : z ≫ f = x) {n : ℕ} {c : Fin n → L} {w : Fin n → (epsAt z ⟶ G')}
    {w' : Fin n → (epsAt x ⟶ G)} {v : epsAt z ⟶ G'} {v' : epsAt x ⟶ G} (hw : ∀ k, (w k).left ≫ φ = (w' k).left)
    (hv : IsComb c w v) (hv' : IsComb c w' v') : v.left ≫ φ = v'.left := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨u', hu', rfl⟩ := hv'
  let ρ : epsAt (z ≫ f) ⟶ Over.mk ((epsAt z).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let P := (preHom ρ).comp (pushHom h (epsAt z))
  have hP : ∀ a, (P a).left = a.left ≫ φ := fun a => Category.id_comp _
  have e : u' = fun k => P (u k) := by
    funext k
    ext1
    rw [hP, hu, hu', Category.assoc, hw]
  rw [← hP, map_list_prod, List.map_ofFn, e]
  rfl

theorem frame_vals {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    {Z : CptOver Y U} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li} (ht : CptIn.IsTie Z 𝔐 i j)
    {z : Spec (CommRingCat.of L) ⟶ 𝔐.X} (hc : genPt 𝔐.ξ ⤳ centre z) {y₀ : Sp L ⟶ Xo.XF c}
    (hz : z ≫ 𝔐.f = y₀ ≫ Y.j) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z)) {Λ : Lat (Z.ξ₀ ≫ Y.j) Z.V} {V : Lat 𝔐.ξ 𝔐.Li}
    {n : ℕ} {b : Fin n → Z.V} (hb : Λ.IsFrameAt b ⟨𝔐.f (centre z), h⟩)
    (hV : V ⟨centre z, hc⟩ = Λ.pull 𝔐.ξ 𝔐.f j ⟨centre z, hc⟩) {v : Vecs y₀ n} (hv : Rep.IsValFam Z y₀ b v)
    {σ : 𝓞 E →+* L} (hve : IsEigFrame Xo.univ.t.act (under y₀) σ v) {bp : Fin n → 𝔐.Li}
    (hbp : V.IsFrameAt bp ⟨centre z, hc⟩) {vb : Fin n → (epsAt z ⟶ 𝔐.t.G)} (hvb : ∀ k, 𝔐.M.ValAt z (bp k) (vb k)) :
    ∃ (d : Ω) (r : L) (A : Matrix (Fin n) (Fin n) L) (v' : Vecs y₀ n), r * A.det = 1 ∧ ValAt 𝔐.ξ z d r ∧
      exteriorPower.ιMulti Ω n (fun k => j (b k)) = d • exteriorPower.ιMulti Ω n bp ∧
      IsEigFrame Xo.univ.t.act (under y₀) σ v' ∧ (∀ k, IsComb (A k) v (v' k)) ∧ ∀ k, Tied 𝔐 z y₀ (vb k) (v' k) := by
  have hξ := 𝔐.tie.gen
  obtain ⟨T, T', hTT, hT, hT'⟩ := frame_change _ _ _ _ _ _ 𝔐.f i _ _ j Λ V ⟨centre z, hc⟩ h n b bp ht.1 hξ ht.2.2.1 hb hV hbp
  set gm := genMap 𝔐.ξ ⟨centre z, hc⟩ with hgm
  let ρ : 𝔐.X.presheaf.stalk (centre z) →+* L := (Scheme.stalkClosedPointTo z).hom
  have hw : ∀ a, ∃ w, 𝔐.M.ValAt z (j (b a)) w := fun a => by
    obtain ⟨w, h1, -⟩ := val_of_comb 𝔐.M hc bp vb hvb (T a)
    exact ⟨w, (hT a).symm ▸ h1⟩
  choose w hw using hw
  have hcomb : ∀ k, IsComb (fun a => ρ (T' k a)) w (vb k) := fun k => by
    obtain ⟨w', h1, h2⟩ := val_of_comb 𝔐.M hc (fun a => j (b a)) w hw (T' k)
    rw [← hT' k] at h1
    rwa [LieModel.ValAt.unique hξ (hvb k) h1]
  obtain ⟨W, _, _, Mu, Mz, act, hMu, -, hsame⟩ := GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y L y₀
  choose e he using fun a => Mu.onto (v a) (hve.1 a).1
  obtain rfl : v = fun a => Mu.pt (e a) := funext fun a => (he a).symm
  have hwe : ∀ a, (w a).left ≫ 𝔐.m.φ = (Mz.pt (e a)).left := fun a => by
    obtain ⟨v', h1, h2⟩ := hv a
    rw [(hsame (e a)).unique h2]
    exact tie_val ht hz.symm h1 (hw a)
  let A : Matrix (Fin n) (Fin n) L := ρ.mapMatrix T'
  let B : Matrix (Fin n) (Fin n) L := ρ.mapMatrix T
  have hBA : B * A = 1 := by rw [← map_mul, hTT, map_one]
  have hAB : A * B = 1 := mul_eq_one_comm.1 hBA
  let e' : Fin n → W := fun k => ∑ a, A k a • e a
  obtain ⟨he1, he2⟩ := (GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ L _ _ W Mu _ Xo.univ.t.act act σ n e hMu).1 hve
  have hsum : ∀ cf : Fin n → L, ∑ k, cf k • e' k = ∑ a, (Matrix.vecMul cf A) a • e a := fun cf => by
    simp only [e', Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have hdet : T.det * T'.det = 1 := by rw [← Matrix.det_mul, hTT, Matrix.det_one]
  have hAd : A.det = ρ T'.det := (RingHom.map_det ρ T').symm
  refine ⟨gm T.det, ρ T.det, A, fun k => Mu.pt (e' k), by rw [hAd, ← map_mul, hdet, map_one], ⟨hc, T.det, rfl, rfl⟩, ?_,
    (GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ L _ _ W Mu _ Xo.univ.t.act act σ n e' hMu).2 ⟨fun k => ?_, fun x hx => ?_⟩,
    fun k => (GlobalTheory.T.is_comb_tangent_iff_linear_sum _ L _ _ W Mu n e _ _).2 rfl, fun k => ⟨Mz.pt (e' k), hsame _, ?_⟩⟩
  · have e := GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := 𝔐.Li)) (gm.mapMatrix T) bp
    have e2 : (fun k => j (b k)) = fun a => ∑ k, (gm.mapMatrix T) a k • bp k := funext hT
    rw [e2, e, RingHom.map_det]
  · exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (he1 a)
  · obtain ⟨cf, hcf, hu⟩ := he2 x hx
    refine ⟨Matrix.vecMul cf B, ?_, fun cf' hcf' => ?_⟩
    · show x = _
      rw [hsum, Matrix.vecMul_vecMul, hBA, Matrix.vecMul_one]
      exact hcf
    · have : Matrix.vecMul cf' A = cf := hu _ (hcf'.trans (hsum cf'))
      rw [← this, Matrix.vecMul_vecMul, hAB, Matrix.vecMul_one]
  · exact comb_push 𝔐.m.cart hz hwe (hcomb k) ((GlobalTheory.T.is_comb_tangent_iff_linear_sum _ L _ _ W Mz n e _ _).2 rfl)

end VP

open VP in

theorem valuePhi : ValuePhi := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j a b a' b' φ L _ _ s z bp bq vp vq α κ u ht hl hg hr ha'
    hb' hint hcst hfp hfq hvp hvq hap hbq hu
  have hc : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) ∧ IsNoetherianRing (𝓞 c.F) ∧
      ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧ x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    refine ⟨IsFractionRing.injective (𝓞 c.F) c.F, inferInstance, fun x => ?_⟩
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
    have hq0 : algebraMap (𝓞 c.F) c.F q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    exact ⟨p, q, hq0, div_mul_cancel₀ _ hq0⟩
  obtain ⟨y₀, hz, hU, hs, h, hT⟩ := exists_point E H D l Xo c Y U Z S Ω K J y 𝔐 i j s z hc ht hint hcst
  have hτ : τ.1 (H.rt : E) = H.rt0 := τ.2
  obtain ⟨hv1, hv2, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c _ _ Y U Z τ.1 hβ hτ
  obtain ⟨W₁, hW₁, b₁, -, hb₁⟩ := hv1 _ hT
  have hb₁x := hb₁ _ hT hW₁
  obtain ⟨W₂, hW₂, b₂, -, hb₂⟩ := hv2 _ hT
  have hb₂x := hb₂ _ hT hW₂
  obtain ⟨v, hvv, hve⟩ := GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c _ _ Y U Z τ.1 hβ hτ L s y₀ hs hU h τ.1 D.p b₁ hb₁x
  obtain ⟨w, hwv, hwe⟩ := GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c _ _ Y U Z τ.1 hβ hτ L s y₀ hs hU h
    (ComplexEmbedding.conjugate τ.1) D.q b₂ hb₂x
  have hfr : IsFramed U τ.1 s y₀ v w := ⟨hs, hU, hve, hwe⟩
  obtain ⟨-, -, hgen⟩ := hg
  obtain ⟨A₁, B₁, hA₁, hB₁, hw1, hw2, -⟩ := hgen _ hT
  obtain ⟨α₀, ha₀⟩ := coeff_of_span hA₁ (hw1.symm.trans (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hb₁x).1)
  obtain ⟨κ₀, hb₀⟩ := coeff_of_span hB₁ (hw2.symm.trans (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hb₂x).1)
  have hRep := hr L s y₀ v w b₁ b₂ α₀ κ₀ hfr ha₀ hb₀ hvv hwv
  obtain ⟨-, hst1, hst2⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j ht ⟨centre z, hc⟩ (mem_genFibre _ z hc)
  have hcen : centre (y₀ ≫ Y.j) = 𝔐.f (centre z) := by rw [← hz]; rfl
  have h' : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z) := hcen ▸ h
  have hpt : (⟨centre (y₀ ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) = ⟨𝔐.f (centre z), h'⟩ := Subtype.ext hcen
  rw [hpt] at hb₁x hb₂x
  obtain ⟨d₁, r₁, A, v', hr₁, hd₁, hι₁, hv'e, hA, ht₁⟩ := frame_vals ht hc hz h' hb₁x hst1 hvv hve hfp hvp
  obtain ⟨d₂, r₂, B, w', hr₂, hd₂, hι₂, hw'e, hB, ht₂⟩ := frame_vals ht hc hz h' hb₂x hst2 hwv hwe hfq hvq
  have hfr' : IsFramed U τ.1 s y₀ v' w' := ⟨hs, hU, hv'e, hw'e⟩
  have hne₁ := (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hfp).2
  have hne₂ := (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hfq).2
  have eα : α = i α₀ * d₁ := by
    have e := (ha' b₁ α₀ ha₀).symm.trans hap
    rw [hι₁, smul_smul] at e
    exact (smul_left_injective Ω hne₁ e).symm
  have eκ : κ = i κ₀ * d₂ := by
    have e := (hb' b₂ κ₀ hb₀).symm.trans hbq
    rw [hι₂, smul_smul] at e
    exact (smul_left_injective Ω hne₂ e).symm
  have hr₂0 : r₂ ≠ 0 := left_ne_zero_of_mul_eq_one hr₂
  rw [← hz] at hRep
  have hRep' := val_pull₀ ht.1 z hc hRep
  have hval := FV.mul (FV.mul hRep' hd₁) (FV.inv hd₂ hr₂0)
  have hαk : α / κ = i (α₀ / κ₀) * d₁ * d₂⁻¹ := by
    rw [eα, eκ, map_div₀]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [← hαk] at hval
  have hchg := hl.chg L s y₀ v w v' w' A B hfr hfr' hA hB
  refine ⟨y₀, v', w', hz, hfr', ?_, ht₁, ht₂⟩
  rw [FV.unique hu hval, ← eq_inv_of_mul_eq_one_right hr₂]
  linear_combination r₁ * hchg - φ L y₀ v' w' * hr₁

end RootFieldNumerics.RF
