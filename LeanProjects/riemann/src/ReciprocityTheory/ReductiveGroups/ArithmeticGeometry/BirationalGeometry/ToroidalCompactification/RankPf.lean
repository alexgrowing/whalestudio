import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Chart

variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)

include hx in
theorem tvec_inj {c c' : Fin n → R} (h : tvec (x := x) c = tvec (x := x) c') : c = c' := by
  rw [← tcoord_tvec hx c, ← tcoord_tvec hx c']
  exact tcoord_congr hx h _ _

theorem list_prod_tan' : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := R) (DualNumber R) ⟶ Gx)) (hu : ∀ i, IsTan (u i)),
    ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i)
  | 0, u, hu => by
    have e0 : (List.ofFn u).prod = 1 := by simp
    refine ⟨e0 ▸ isTan_one, ?_⟩
    rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
    simp
  | M + 1, u, hu => by
    obtain ⟨h, e⟩ := list_prod_tan' (fun i => u i.succ) (fun i => hu i.succ)
    have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
    rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]

theorem mem_eigLat_iff {O : Type} (act : O → (Gx ⟶ Gx)) [∀ a, IsMonHom (act a)] (χ : O → R) (c : Fin n → R) :
    c ∈ eigLat hx act χ ↔ ∀ a, tmap hx (act a) c = χ a • c := by
  simp only [eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem tvec_eig_iff (e : Gx ⟶ Gx) [IsMonHom e] (c : Fin n → R) (s : R) :
    tvec (x := x) c ≫ e = spMap (scaleD s) ≫ tvec (x := x) c ↔ tmap hx e c = s • c := by
  rw [← tvec_tmap hx, ← tvec_smul hx]
  exact ⟨fun h => tvec_inj hx h, fun h => by rw [h]⟩

end Chart

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)

include hc in
theorem rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact rel_uniq_v h₁ h₂
  · rintro rfl
    exact rel_uniq_w hc h₁ h₂

include hc hg in
theorem tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1

include hc in
theorem eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = Geo.Tor.spMap (Geo.Tor.epsScale s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)

include hc hg hab hact' in

theorem finrank_of_lieMult {N : ℕ} (hL : Geo.Tor.LieMult act tk τ N) :
    Module.finrank k (eigLat hx act' (fun a => τ a)) = N := by
  obtain ⟨vB, hvB, huq⟩ := hL
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  choose v' hv' using fun i => rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) (vB i)
  have hv'e : ∀ i, IsTan (v' i) ∧ ∀ a, v' i ≫ act' a = spMap (scaleD (τ a)) ≫ v' i :=
    fun i => (hT _ _ (hv' i)).mp (hvB i)
  let bb : Fin N → Fin n → k := fun i => tcoord hx (v' i) (hv'e i).1
  have htv : ∀ i, tvec (x := x) (bb i) = v' i := fun i => (tcoord_spec hx _ _).symm
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔ ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  have hbW : ∀ i, bb i ∈ eigLat hx act' (fun a => τ a) := fun i => (hmem _).mpr fun a => by
    rw [htv]
    exact (hv'e i).2 a
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ v' i).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv' i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • bb i) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ v' i) (fun i => isTan_scale (d i) (hv'e i).1)
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ => tcoord_scale hx (d i) (hv'e i).1
  have hsum : ∀ d : Fin N → k, (∑ i, d i • bb i) ∈ eigLat hx act' (fun a => τ a) := fun d =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbW i)
  have hWeig : ∀ d : Fin N → k, Geo.Tor.IsLieEigen act tk τ (Wd d) := fun d => (hT _ _ (hPW d)).mpr
    ⟨by rw [hPeq]; exact isTan_tvec hx _, by rw [hPeq]; exact (hmem _).mp (hsum d)⟩
  have hsat : ∀ d : Fin N → k, ∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ Wd d = (List.ofFn u).prod :=
    fun d => ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, rfl⟩
  have hli : LinearIndependent k bb := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have e1 : P d = P 0 := by
      rw [hPeq, hPeq, hd]
      simp
    have e2 : Wd d = Wd 0 := (rel_eq_iff hc (hPW d) (hPW 0)).mpr e1
    have := (huq (Wd 0) (hWeig 0)).unique (e2 ▸ hsat d) (hsat 0)
    exact fun i => congrFun this i
  have hspan : eigLat hx act' (fun a => τ a) = Submodule.span k (Set.range bb) := by
    apply le_antisymm
    · intro c hc'
      obtain ⟨w, hw⟩ := rel_exists_w hc hg (tvec (x := x) c)
      obtain ⟨d, ⟨u, hu, hwu⟩, -⟩ := huq w ((hT _ _ hw).mpr ⟨isTan_tvec hx c, (hmem c).mp hc'⟩)
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      have e1 : w = Wd d := by rw [hwu, hu']
      have e2 : tvec (x := x) c = P d := rel_uniq_v (e1 ▸ hw) (hPW d)
      rw [hPeq] at e2
      rw [tvec_inj hx e2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbW i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Count

section Assembly

theorem pushR_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) (e : G ⟶ G) :
    pushR G (y ≫ (Over.pullback (fB R R')).map e) = pushR G y ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

end Assembly

end ReciprocityTheory.ChartRestriction.G.Chart
