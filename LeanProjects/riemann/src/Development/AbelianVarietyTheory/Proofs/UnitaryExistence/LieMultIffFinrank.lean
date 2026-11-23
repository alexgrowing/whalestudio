import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.LieExt

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)

include hc hg hab hact' in

theorem lieMult_of_finrank {N : ℕ} (hN : Module.finrank k (eigLat hx act' (fun a => τ a)) = N) :
    Geo.Tor.LieMult act tk τ N := by
  let B := Module.finBasisOfFinrankEq k _ hN
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔
      ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  choose vB hv using fun i => rel_exists_w hc hg (tvec (x := x) (B i : Fin n → k))
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k)).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • (B i : Fin n → k)) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k))
      (fun i => isTan_scale (d i) (isTan_tvec hx _))
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      (tcoord_scale hx (d i) (isTan_tvec hx _)).trans (by rw [tcoord_tvec])
  refine ⟨vB, fun i => (hT _ _ (hv i)).2 ⟨isTan_tvec hx _, (hmem _).1 (B i).2⟩, fun w hw => ?_⟩
  obtain ⟨v, hwv⟩ := rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) w
  obtain ⟨ht, he⟩ := (hT _ _ hwv).1 hw
  obtain ⟨c, rfl⟩ : ∃ c, tvec (x := x) c = v := ⟨_, (tcoord_spec hx v ht).symm⟩
  let c' : eigLat hx act' (fun a => τ a) := ⟨c, (hmem c).2 he⟩
  have key : ∀ d : Fin N → k, (∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ w = (List.ofFn u).prod) ↔
      B.equivFun c' = d := fun d => by
    have e₁ : B.equivFun c' = d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
      simp [c']
    have e₂ : w = Wd d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      refine (rel_eq_iff hc hwv (hPW d)).trans ?_
      rw [hPeq]
      exact ⟨fun h => tvec_inj hx h, fun h => by rw [← h]⟩
    rw [e₁, ← e₂]
    constructor
    · rintro ⟨u, hu, hwu⟩
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      rw [hwu, hu']
    · intro h
      exact ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, h⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

end Count

theorem lieMult_iff_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] {n : ℕ} {xc : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
    {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) [∀ a, IsMonHom (act.act a)] (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (fB k K) ((algebraMap k K).comp χ) N ↔
      Module.finrank k (eigLat hx act.act χ) = N := by
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := k) (R' := K) G n xc hx
  have hpt : ∀ c : Fin n → k, pushR G (tvec (x := x') (algebraMap k K ∘ c)) =
      spMap (dualMapA k K) ≫ tvec (x := xc) c := fun c =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp c]; rfl)
  have hLk : ∀ a (c : Fin n → k), tmap hx' ((Over.pullback (fB k K)).map (act.act a)) (algebraMap k K ∘ c) =
      algebraMap k K ∘ tmap hx (act.act a) c := by
    intro a c
    apply tvec_inj hx'
    apply pushR_inj G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hx, Category.assoc]
  have e0 : Module.finrank k (eigLat hx act.act χ) =
      Module.finrank K (eigLat hx' (fun a => (Over.pullback (fB k K)).map (act.act a))
        (fun a => (algebraMap k K).comp χ a)) :=
    finrank_eig_bc (fun a => tmap hx (act.act a))
      (fun a => tmap hx' ((Over.pullback (fB k K)).map (act.act a))) hLk χ
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  rw [e0]
  exact ⟨finrank_of_lieMult (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _,
    lieMult_of_finrank (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _⟩

theorem lieMult_extend_iff {k K : Type} [Field k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (Geo.Tor.spMap φ) (φ.comp χ) N ↔ Geo.Tor.LieMult act (𝟙 _) χ N := by
  let _ := φ.toAlgebra
  have := act.hom
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have h := lieMult_iff_finrank (K := k) G hx act χ N
  have e : fB k k = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [e, Algebra.algebraMap_self, RingHom.id_comp] at h
  exact (lieMult_iff_finrank (K := K) G hx act χ N).trans h.symm

theorem exists_comp_eq {k K O : Type} [Field k] [IsAlgClosed k] [Field K] [CommRing O] [Algebra.IsIntegral ℤ O]
    (φ : k →+* K) (τ : O →+* K) : ∃ χ : O →+* k, φ.comp χ = τ := by
  let _ := φ.toAlgebra
  have h : ∀ a, ∃ z : k, φ z = τ a := fun a => by
    have hi : IsIntegral k (τ a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map τ.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))
  choose f hf using h
  have inj := φ.injective
  exact ⟨⟨⟨⟨f, inj (by simp [hf])⟩, fun a b => inj (by simp [hf])⟩, inj (by simp [hf]),
    fun a b => inj (by simp [hf])⟩, RingHom.ext hf⟩

theorem detCond_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (D : Geo.Tor.Datum H)
    {k K : Type} [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] (act : Geo.Tor.OAct (𝓞 E) G) {ρ : k} (h : Geo.Tor.DetCond D act (𝟙 _) ρ) :
    Geo.Tor.DetCond D act (Geo.Tor.spMap φ) (φ ρ) := by
  intro τ
  obtain ⟨χ, rfl⟩ := exists_comp_eq φ τ
  rw [lieMult_extend_iff, lieMult_extend_iff]
  exact ⟨fun e => (h χ).1 (φ.injective e), fun e => (h χ).2 fun e' => e (congrArg φ e')⟩

end GlobalTheory.LieExt
