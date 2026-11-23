import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CarriedCubeGen

section
variable {X Y Y₀ : Scheme.{0}} {L : LB X}

abbrev TestClass (L : LB X) (Y : Scheme.{0}) : Type 1 :=
  ∀ (f : X ⟶ X) (_ : LB.Iso L (L.pull f)) (Z : Scheme.{0}) (_ _ : Z ⟶ Y), Prop

def CTriv (L : LB X) (Y : Scheme.{0}) (A : TestClass L Y)
    (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ f w Z r r', A f w Z r r' → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι), Good L z J → Good L z J' →
      val t r' z J' = F _ (fun ψ => gw w (r ≫ ψ) z (J' ((r ≫ ψ) ≫ f)) (J (r ≫ ψ))) * val t r z J

variable {A : TestClass L Y}

theorem CTriv.congr {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (e : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = F' U g) : CTriv L Y A F' := by
  obtain ⟨K, _, φ, ε, t, ht, e₁, e₂⟩ := h
  exact ⟨K, inferInstance, φ, ε, t, ht, fun U _ g => (e₁ U g).trans (e U g),
    fun f w Z r r' hA z J J' hJ hJ' => (e₂ f w Z r r' hA z J J' hJ hJ').trans (by rw [e])⟩

theorem CTriv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (h' : CTriv L Y A F') : CTriv L Y A (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e', c'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g)),
    fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  rw [val_mul hJ', val_mul hJ, c f w Z r r' hA z J J' hJ hJ', c' f w Z r r' hA z J J' hJ hJ']
  exact _root_.mul_mul_mul_comm _ _ _ _

theorem CTriv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F) :
    CTriv L Y A (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_,
    fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, e U g]
  · rw [val_inv, val_inv, c f w Z r r' hA z J J' hJ hJ', mul_inv]

theorem CTriv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (g : Y ⟶ X) (hg : ∀ (U : Type) [CommGroup U] (u : (Y ⟶ X) → U), F U u = u g) :
    ∃ t : LB.Gen (L.pull g), t.IsGen ∧ ∀ f w Z r r', A f w Z r r' → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι),
      Good L z J → Good L z J' →
      val t r' z J' = gw w (r ≫ g) z (J' ((r ≫ g) ≫ f)) (J (r ≫ g)) * val t r z J := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨t', ht', hv⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => g) (ε' := fun _ => 1)
    (fun U _ u => by rw [e, hg]; simp) t ht
  refine ⟨t', ht', fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  rw [hv _ _ z J hJ, hv _ _ z J' hJ', c f w Z r r' hA z J J' hJ hJ', hg]

theorem ctriv_of_pmaps {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (p : Y ⟶ Y₀)
    (hA : ∀ f w Z r r', A f w Z r r' → ∃ h : Y₀ ⟶ Y₀, PMaps w φ φ ε t t h ∧ (∀ k, φ k ≫ f = h ≫ φ k) ∧
      r' ≫ p = (r ≫ p) ≫ h) :
    CTriv L Y A (fun _ _ g => ∏ k, g (p ≫ φ k) ^ ε k) := by
  refine ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun f w Z r r' H z J J' hJ hJ' => ?_⟩
  obtain ⟨h, hm, hc, e⟩ := hA f w Z r r' H
  rw [val_pull hJ', val_pull hJ, e, val_of t _ z J' (fun k => J' (((r ≫ p) ≫ φ k) ≫ f))
    (fun k => by simp only [Category.assoc, hc]),
    hm Z (r ≫ p) z _ (fun k => J ((r ≫ p) ≫ φ k)) (fun k => hJ' (((r ≫ p) ≫ φ k) ≫ f))
      (fun k => hJ ((r ≫ p) ≫ φ k))]
  refine congrArg₂ (· * ·) ?_ rfl
  simp only [Category.assoc]

theorem gm_stalk {Z : Scheme.{0}} (κ : Z ⟶ Y) (z : Z) (r : Y ⟶ X) (U : X.Opens) (h : r (κ z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  rw [gm_val (κ ≫ r) z U h]
  show _ = (κ.stalkMap z).hom (gm r (κ z) U a).val
  rw [gm_val r (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem gs_stalk {Z : Scheme.{0}} (κ : Z ⟶ Y) (z : Z) (r : Y ⟶ X) (U : X.Opens) (h : r (κ z) ∈ U)
    (a : Γ(X, U)) : gs (κ ≫ r) z U a = (κ.stalkMap z).hom (gs r (κ z) U a) := by
  rw [gs_eq (κ ≫ r) z U h, gs_eq r (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem secCarried_along {θ : L.Sec} {f : X ⟶ X} {w : LB.Iso L (L.pull f)} (h : SecCarried L θ f w)
    {Z : Scheme.{0}} (ψ : Z ⟶ X) (z : Z) (j k : L.ι) (hk : ψ z ∈ L.U k) (hj : f (ψ z) ∈ L.U j) :
    gs (ψ ≫ f) z (L.U j) (θ.f j) = (gw w ψ z j k).val * gs ψ z (L.U k) (θ.f k) := by
  have e := congrArg (ψ.stalkMap z).hom (h (ψ z) j k hk hj)
  have e₁ := gs_stalk ψ z (𝟙 X) (L.U k) hk (θ.f k)
  have e₂ := gm_stalk ψ z (𝟙 X) ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ (w.s (fun _ => j, k))
  rw [Category.comp_id] at e₁ e₂
  rw [gs_stalk ψ z f _ hj, gs_eq f _ _ hj, e, map_mul, e₁, gs_eq (𝟙 X) (ψ z) _ hk, gw, gw, e₂]
  rfl

theorem ctriv_of_sec (θ : L.Sec) (g : Y ⟶ X) (hg : ∀ y, g y ∈ secNz θ)
    (hA : ∀ f w Z r r', A f w Z r r' → SecCarried L θ f w ∧ r' ≫ g = (r ≫ g) ≫ f) :
    CTriv L Y A (fun _ _ u => u g) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ g).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hg y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ g hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  let t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ ↦ g) fun _ ↦ ((1 : ℕ) : ℤ)) := ⟨fun j => (hu j).unit⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      (val t r z J).val = gs (r ≫ g) z (L.U (J (r ≫ g))) (θ.f _) := fun Z r z J hJ => by
    have hm := hJ.mem (fun _ : Fin 1 => g) r
    exact (gs_unit r z _ hm _).symm.trans ((gs_res r z (LB.wchart_le L (fun _ : Fin 1 => g) _ 0) hm _).trans
      (gs_pull r g z _ (hJ (r ≫ g)) _))
  refine ⟨Fin 1, inferInstance, _, _, t,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ g).compat i j), fun U _ u => by simp,
    fun f w Z r r' H z J J' hJ hJ' => Units.ext ?_⟩
  obtain ⟨hs, e⟩ := hA f w Z r r' H
  rw [Units.val_mul, hv _ _ z J hJ, hv _ _ z J' hJ', e]
  exact secCarried_along hs (r ≫ g) z _ _ (hJ _) (hJ' ((r ≫ g) ≫ f))

theorem stalk_units_injective {Z : Scheme.{0}} (i : Z ⟶ Y) [IsOpenImmersion i] (z : Z) :
    Function.Injective (Units.map (i.stalkMap z).hom.toMonoidHom) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (i.stalkMap z)).1 (congrArg Units.val h))

theorem exists_units (x : Y ⟶ X) (W : Y.Opens) (t : LB.Gen (L.pull (W.ι ≫ x))) :
    ∃ τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (k : L.ι), x (W.ι (r z)) ∈ L.U k →
      gm (r ≫ W.ι) z _ (τ k) = gm r z (LB.wchart L (fun _ : PUnit => W.ι ≫ x) (fun _ => k)) (t.s fun _ => k) := by
  have le : ∀ k, W.ι ⁻¹ᵁ (W ⊓ x ⁻¹ᵁ L.U k) ≤ LB.wchart L (fun _ : PUnit => W.ι ≫ x) (fun _ => k) :=
    fun k y hy => Set.mem_iInter.2 fun _ => hy.2
  have ex : ∀ k, ∃ u : Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, pullU W.ι _ u = res (le k) (t.s fun _ => k) := fun k => by
    have : IsIso (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k)) := W.ι.isIso_app _ (by simp)
    refine ⟨Units.map (CategoryTheory.inv (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k))).hom.toMonoidHom
      (res (le k) (t.s fun _ => k)), Units.ext ?_⟩
    exact CategoryTheory.IsIso.inv_hom_id_apply (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k)) _
  choose τ hτ using ex
  refine ⟨τ, fun Z r z k hk => ?_⟩
  have hm : W.ι (r z) ∈ W ⊓ x ⁻¹ᵁ L.U k := ⟨(r z).2, hk⟩
  rw [← gm_pull r W.ι z _ hm, hτ]
  exact gm_res r z (le k) hm _

theorem exists_frame (hL : L.IsLB) (x : Y ⟶ X) (W : Y.Opens) (t : LB.Gen (L.pull (W.ι ≫ x))) (ht : t.IsGen) :
    ∃ τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, FrameAlong L x W τ ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y), x ≫ f = h ≫ x →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W), r' ≫ W.ι = (r ≫ W.ι) ≫ h → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι),
          Good L z J → Good L z J' → val t r' z J' =
            gw w (r ≫ W.ι ≫ x) z (J' ((r ≫ W.ι ≫ x) ≫ f)) (J (r ≫ W.ι ≫ x)) * val t r z J) →
        FrameCarriedAlong L x W τ f w h := by
  obtain ⟨τ, hτ⟩ := exists_units x W t
  refine ⟨τ, fun z k k' hz hk hk' => ?_, fun f w h hx H z j k hz hz' hk hj => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y : W, W.ι y = z := ⟨⟨z, hz⟩, rfl⟩
    apply stalk_units_injective W.ι y
    have a := hτ _ (𝟙 _) y k hk
    have a' := hτ _ (𝟙 _) y k' hk'
    rw [Category.id_comp] at a a'
    rw [map_mul, ← gm_stalk W.ι y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k) ⟨hz, hk⟩,
      ← gm_stalk W.ι y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k') ⟨hz, hk'⟩,
      ← gm_stalk W.ι y x (L.U k ⊓ L.U k') ⟨hk, hk'⟩, Category.comp_id, a, a']
    refine (gen_trans ht (𝟙 _) y (j := fun _ => k) (j' := fun _ => k') (Set.mem_iInter.2 fun _ => hk)
      (Set.mem_iInter.2 fun _ => hk')).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (Fintype.prod_unique _).trans ((zpow_one _).trans ?_)
    rw [Category.id_comp]
  · obtain ⟨Z, i, hi, r, r', y, rfl, e, e'⟩ : ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsOpenImmersion i) (r r' : Z ⟶ W)
        (y : Z), i y = z ∧ r ≫ W.ι = i ∧ r' ≫ W.ι = i ≫ h :=
      ⟨(W ⊓ h ⁻¹ᵁ W : Y.Opens), (W ⊓ h ⁻¹ᵁ W).ι, inferInstance, Y.homOfLE inf_le_left,
        IsOpenImmersion.lift W.ι ((W ⊓ h ⁻¹ᵁ W).ι ≫ h) (by
          rintro _ ⟨y, rfl⟩
          exact ⟨⟨h y.1, y.2.2⟩, rfl⟩), ⟨z, hz, hz'⟩, rfl, Scheme.homOfLE_ι _ _, IsOpenImmersion.lift_fac _ _ _⟩
    subst e
    have hfx : f (x (W.ι (r y))) ∈ L.U j := by
      have : (x ≫ f) (W.ι (r y)) = (h ≫ x) (W.ι (r y)) := by rw [hx]
      exact (show f (x (W.ι (r y))) = x (h (W.ι (r y))) from this) ▸ hj
    have hj' : x (W.ι (r' y)) ∈ L.U j := by
      have : (r' ≫ W.ι) y = ((r ≫ W.ι) ≫ h) y := by rw [e']
      exact (show W.ι (r' y) = h (W.ι (r y)) from this) ▸ hj
    obtain ⟨J, hJ, eJ⟩ := exists_good L hL y (fun _ : PUnit => r ≫ W.ι ≫ x) (fun _ => k) (fun _ _ _ => rfl)
      (fun _ => hk)
    obtain ⟨J', hJ', eJ'⟩ := exists_good L hL y (fun _ : PUnit => (r ≫ W.ι ≫ x) ≫ f) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hfx)
    have c := H Z r r' e' y J J' hJ hJ'
    rw [val_of t r y J (fun _ => k) eJ, val_of t r' y J' (fun _ => j) (fun u => by
      rw [← eJ' u, ← Category.assoc, e']; simp only [Category.assoc, hx]), eJ ⟨⟩, eJ' ⟨⟩,
      ← hτ _ r y k hk, ← hτ _ r' y j hj', e'] at c
    apply stalk_units_injective (r ≫ W.ι) y
    rw [map_mul, ← gm_stalk (r ≫ W.ι) y h (W ⊓ x ⁻¹ᵁ L.U j) ⟨hz', hj⟩,
      ← gm_stalk (r ≫ W.ι) y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k) ⟨hz, hk⟩, Category.comp_id, c]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [← Category.assoc]
    exact gm_stalk (r ≫ W.ι) y x ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hfx, hk⟩ _

end

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {f : G.left ⟶ G.left} {fS : S ⟶ S}

theorem exists_subgroup (hc : IsGrpPullback G G fS f) (h : T.left ⟶ T.left) (hh : h ≫ T.hom = T.hom ≫ fS) :
    ∃ H : Subgroup (T ⟶ G), ∀ g, g ∈ H ↔ g.left ≫ f = h ≫ g.left :=
  ⟨(pushHom hc T).eqLocus (preHom (Over.homMk h hh : Over.mk (T.hom ≫ fS) ⟶ T)), fun _ =>
    ⟨fun e => congrArg (fun q => q.left) e, fun e => Over.OverMorphism.ext e⟩⟩

theorem lift_comm [IsCommMonObj G] (hc : IsGrpPullback G G fS f) (h : T.left ⟶ T.left)
    (hh : h ≫ T.hom = T.hom ≫ fS) (x u v : T ⟶ G) (hx : x.left ≫ f = h ≫ x.left) (hu : u.left ≫ f = h ≫ u.left)
    (hv : v.left ≫ f = h ≫ v.left) :
    (lift x (lift u v)).left ≫ (cubeMapOf hc).F3 = h ≫ (lift x (lift u v)).left := by
  let U : Over.mk (T.hom ≫ fS) ⟶ T := Over.homMk h hh
  let V : Over.mk (T.hom ≫ fS) ⟶ Over.mk ((G3 G).hom ≫ fS) := Over.homMk (lift x (lift u v)).left (by
    show (lift x (lift u v)).left ≫ (G3 G).hom ≫ fS = T.hom ≫ fS
    rw [← Category.assoc, Over.w])
  have key : ∀ (i : Fin 3) (g : T ⟶ G), lift x (lift u v) ≫ x3 G i = g → g.left ≫ f = h ≫ g.left →
      V ≫ pushPt hc.1.w (x3 G i) = U ≫ g := fun i g e hg => Over.OverMorphism.ext (by
    show (lift x (lift u v)).left ≫ (x3 G i).left ≫ f = h ≫ g.left
    rw [← Category.assoc, ← Over.comp_left, e, hg])
  have e : V ≫ lift (pushPt hc.1.w (x3 G 0)) (lift (pushPt hc.1.w (x3 G 1)) (pushPt hc.1.w (x3 G 2))) =
      U ≫ lift x (lift u v) := by
    rw [comp_lift, comp_lift, comp_lift, comp_lift, key 0 x (by simp [x3]) hx, key 1 u (by simp [x3]) hu,
      key 2 v (by simp [x3]) hv]
  exact congrArg (fun q => q.left) e

end

end GlobalTheory.Mum.CarriedCubeGen

namespace GlobalTheory.Mum

open CarriedCubeGen

theorem exists_carried_frame_of_cubeTen {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G')
    (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens)
    (hW : ∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) :
    ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧
      ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)),
        w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS →
        PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w →
        ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left →
          b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  let B : Subgroup (T ⟶ G') := Subgroup.closure {x, a, b, c'}
  have Bx : x ∈ B := Subgroup.subset_closure (by simp)
  have Ba : a ∈ B := Subgroup.subset_closure (by simp)
  have Bb : b ∈ B := Subgroup.subset_closure (by simp)
  have Bc : c' ∈ B := Subgroup.subset_closure (by simp)
  let A : TestClass L.L W := fun f w Z r r' => ∃ (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (hT : T.left ⟶ T.left),
    PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS ∧
    PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 ∧ SecCarried L.L θ f w ∧
    hT ≫ T.hom = T.hom ≫ fS ∧ (∀ g ∈ B, g.left ≫ f = hT ≫ g.left) ∧ r' ≫ W.ι = (r ≫ W.ι) ≫ hT
  have s : ∀ g ∈ cubeTen x a b c', g ∈ B → CTriv L.L W A (fun _ _ u => u (W.ι ≫ g.left)) := fun g hg gB =>
    ctriv_of_sec θ _ (fun y => hW g hg y.2) (by
      rintro f w Z r r' ⟨fS, hc, hT, -, -, hs, -, hB, e⟩
      refine ⟨hs, ?_⟩
      rw [← Category.assoc, e]
      simp only [Category.assoc, hB g gB])
  have cub : ∀ u ∈ B, ∀ v ∈ B, CTriv L.L W A (fun _ _ h =>
      h (W.ι ≫ (x * u * v).left) * (h (W.ι ≫ (x * u).left))⁻¹ * (h (W.ι ≫ (x * v).left))⁻¹ *
        (h (W.ι ≫ (u * v).left))⁻¹ * h (W.ι ≫ x.left) * h (W.ι ≫ u.left) * h (W.ι ≫ v.left) *
        (h (W.ι ≫ (1 : T ⟶ G').left))⁻¹) := fun u hu v hv =>
    (ctriv_of_pmaps (L := L.L) (φ := thφ G' (x3 G')) (ε := thε) c.t c.isGen (W.ι ≫ (lift x (lift u v)).left) (by
      rintro f w Z r r' ⟨fS, hc, hT, -, hm, -, hh, hB, e⟩
      refine ⟨_, hm, fun I => (cubeMapOf hc).psum_comm I.down, ?_⟩
      rw [← Category.assoc, e]
      simp only [Category.assoc, lift_comm hc hT hh x u v (hB x Bx) (hB u hu) (hB v hv)])).congr fun U _ g => by
      simp only [Category.assoc]
      exact prod_cub x u v (fun ψ => g (W.ι ≫ ψ))
  have e : CTriv L.L W A (fun _ _ h => h (W.ι ≫ (1 : T ⟶ G').left)) :=
    (ctriv_of_pmaps (L := L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) L.rig L.rigGen (W.ι ≫ T.hom) (by
      rintro f w Z r r' ⟨fS, hc, hT, hm, -, -, hh, -, e⟩
      refine ⟨_, hm, fun _ => (cubeMapOf hc).e_comm, ?_⟩
      show r' ≫ W.ι ≫ T.hom = (r ≫ W.ι ≫ T.hom) ≫ fS
      rw [← Category.assoc, e]
      simp only [Category.assoc, hh])).congr fun U _ g => by
      rw [Fintype.prod_unique, zpow_one]
      exact congrArg g (Category.assoc _ _ _)
  have Bbc := B.mul_mem Bb Bc
  have s₁ := s (x * a) (by simp [cubeTen]) (B.mul_mem Bx Ba)
  have s₂ := s (x * a⁻¹) (by simp [cubeTen]) (B.mul_mem Bx (B.inv_mem Ba))
  have s₃ := s a (by simp [cubeTen]) Ba
  have s₄ := s a⁻¹ (by simp [cubeTen]) (B.inv_mem Ba)
  have s₅ := s (x * b) (by simp [cubeTen]) (B.mul_mem Bx Bb)
  have s₆ := s (x * c') (by simp [cubeTen]) (B.mul_mem Bx Bc)
  have s₇ := s (x * (b * c')⁻¹) (by simp [cubeTen]) (B.mul_mem Bx (B.inv_mem Bbc))
  have s₈ := s b (by simp [cubeTen]) Bb
  have s₉ := s c' (by simp [cubeTen]) Bc
  have s₀ := s (b * c')⁻¹ (by simp [cubeTen]) (B.inv_mem Bbc)
  have c₁ := cub a Ba a⁻¹ (B.inv_mem Ba)
  have c₂ := cub b Bb c' Bc
  have c₃ := cub (b * c') Bbc (b * c')⁻¹ (B.inv_mem Bbc)
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  obtain ⟨t, ht, hv⟩ := ((t₃.mul t₂.inv).mul e).exists_gen L.isLB (W.ι ≫ x.left) fun U _ g => by
    simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ, hτ, hcar⟩ := exists_frame L.isLB x.left W t ht
  refine ⟨τ, hτ, fun f fS hc w _ hr hm hs hT hh hx ha hb hc' => hcar f w hT hx fun Z r r' er =>
    hv f w Z r r' ⟨fS, hc, hT, hr, hm, hs, hh, ?_, er⟩⟩
  obtain ⟨H, hH⟩ := exists_subgroup hc hT hh
  have le : B ≤ H := (Subgroup.closure_le H).2 (by
    rintro g (rfl | rfl | rfl | rfl)
    exacts [(hH _).2 hx, (hH _).2 ha, (hH _).2 hb, (hH _).2 hc'])
  exact fun g hg => (hH g).1 (le hg)

end GlobalTheory.Mum
