import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CountablePointsOfOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCountable

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PointAlg

section Points

variable {S S' X : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem prod_left (h : IsGrpPullback G' G f φ) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t) {n : ℕ}
    (x' : Fin n → (Over.mk t' ⟶ G')) (x : Fin n → (Over.mk t ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (x i).left) :
    (List.ofFn x').prod.left ≫ φ = (List.ofFn x).prod.left := by
  subst e
  have h1 := map_list_prod (pushHom h (Over.mk t')) (List.ofFn x')
  rw [List.map_ofFn] at h1
  have h2 : (pushHom h (Over.mk t')) ∘ x' = x := funext fun i => Over.OverMorphism.ext (hx i)
  rw [h2] at h1
  exact congrArg (fun z => z.left) h1

omit [GrpObj G] [GrpObj G'] in

theorem exists_lift_pt (h : IsPullback φ G'.hom G.hom f) {t' : X ⟶ S'} (x : X ⟶ G.left) (e : x ≫ G.hom = t' ≫ f) :
    ∃ x' : Over.mk t' ⟶ G', x'.left ≫ φ = x :=
  ⟨Over.homMk (h.lift x t' e) (h.lift_snd _ _ _), h.lift_fst _ _ _⟩

omit [GrpObj G] [GrpObj G'] in

theorem pt_ext (h : IsPullback φ G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

theorem exists_lift_hom {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G f φ) (hH : IsGrpPullback H' H f ψ) (w : G ⟶ H) [IsMonHom w] :
    ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hG (isGrpPullback_pullback G f)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H f) hH
  refine ⟨a.hom ≫ (Over.pullback f).map w ≫ b.hom, inferInstance, ?_⟩
  have e : ((Over.pullback f).map w).left ≫ pullback.fst H.hom f = pullback.fst G.hom f ≫ w.left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', e, ← Category.assoc, ha']

theorem onto_lift {B : Over S} {B' : Over S'} {β : B'.left ⟶ B.left} (hB : IsPullback β B'.hom B.hom f)
    (hG : IsGrpPullback G' G f φ) {n : ℕ} (w : Fin n → (B ⟶ G)) (w' : Fin n → (B' ⟶ G'))
    (hw : ∀ i, (w' i).left ≫ φ = β ≫ (w i).left) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t)
    (h : ∀ y : Over.mk t ⟶ G, ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (y : Over.mk t' ⟶ G') : ∃ x : Fin n → (Over.mk t' ⟶ B'), y = (List.ofFn fun i => x i ≫ w' i).prod := by
  subst e
  obtain ⟨x, hx⟩ := h (pushPt hG.1.w y)
  choose x' hx' using fun i => exists_lift_pt hB (t' := t') (x i).left (Over.w (x i))
  refine ⟨x', pt_ext hG.1 ?_⟩
  rw [prod_left hG rfl _ (fun i => x i ≫ w i) fun i => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hw, ← Category.assoc, hx'], ← hx]
  rfl

end Points

theorem isAbelianScheme_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (Out.powObj G n)
  | 0 => by
    have := hG.comm
    have : IsIso (Out.powObj G 0).hom := inferInstanceAs (IsIso (𝟙 S))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstanceAs (GeometricallyConnected (𝟙 S))⟩
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj G hG n

theorem onto_of_onto {R : Type} [CommRing R] [IsDomain R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {n : ℕ}
    (w : Fin n → (B ⟶ A))
    (h : ∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Fin n → (Over.mk (spMap σ) ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (t : Sp ℂ ⟶ Sp R) (y : Over.mk t ⟶ A) :
    ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod := by
  have := hA.comm
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ Out.powObj B n),
      x ≫ (List.ofFn fun i => Out.powPr B i ≫ w i).prod = (List.ofFn fun i => (x ≫ Out.powPr B i) ≫ w i).prod := by
    intro T x
    have h1 := map_list_prod (preHom (G := A) x) (List.ofFn fun i => Out.powPr B i ≫ w i)
    rw [List.map_ofFn] at h1
    refine h1.trans ?_
    congr 2
  obtain ⟨x, hx⟩ := (OntoSurj.surjective_of_onto_complex_points R σ hσ A (Out.powObj B n)
    (List.ofFn fun i => Out.powPr B i ≫ w i).prod hA (isAbelianScheme_pow B hB n) fun y => by
      obtain ⟨x, hx⟩ := h y
      refine ⟨(Out.powIsLimit B n).lift (Fan.mk _ x), ?_⟩
      rw [key, hx]
      congr 2
      funext i
      exact congrArg (· ≫ w i) ((Out.powIsLimit B n).fac (Fan.mk _ x) ⟨i⟩).symm).2 ℂ t y
  exact ⟨fun i => x ≫ Out.powPr B i, by rw [hx, key]⟩

theorem map_sum_eq_prod {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    {n : ℕ} (z : Fin n → V) : e (∑ i, z i) = (List.ofFn fun i => e (z i)).prod := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    simpa using this.symm
  | succ n ih => rw [Fin.sum_univ_succ, he, ih, List.ofFn_succ, List.prod_cons]

set_option maxHeartbeats 1000000 in

theorem exists_numberField_point_of_cmLat : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  intro hC hPt hT hL E _ _ _ H D l Xo g ty FU i Pe hP p q ⟨Z⟩
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (chartPullPull P₀.L ψ ψ rfl) (chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨ε, a, ha⟩ := exists_pure_vectors_periods_span E H _ g ty Pe hP p q Z
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull (spMap ρ.toRingHom ≫ y) Xo.univ.t
        exact ⟨_, ⟨m'⟩⟩
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end GlobalTheory.PointAlg
