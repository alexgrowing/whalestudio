import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

set_option autoImplicit false

noncomputable section

namespace PositivityTheory.HtPt.Weilfun

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

def wq (θ : A → A → A → U) (N : ℕ) (x z : A) : U := cubN θ N 1 z x * (cubN θ N 1 x z)⁻¹

end Alg

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

theorem exists_weilUnit (c : CubicalStr G L) (N : ℕ) {T : Over S} (x y : T ⟶ G) (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ u : (Γ(T.left, ⊤))ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
      gm ρ.left z ⊤ u = wq (cubV c z J) N (ρ ≫ x) (ρ ≫ y) := by
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_cubN c (1 : T ⟶ G) y x N
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_cubN c (1 : T ⟶ G) x y N
  obtain ⟨t, -, hv⟩ := exists_gen L.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, hx, hy, _root_.one_mul, mul_comm y x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ t₁ (LB.invGen L.L _ _ t₂))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ (DVR.invGen_isGen _ _ _ _ ht₂))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L.L (PEmpty.elim : PEmpty → (T.left ⟶ G.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  have h1 : ρ ≫ (1 : T ⟶ G) = 1 := map_one (preHom ρ)
  have e : val t ρ.left z J = wq (cubV c z J) N (ρ ≫ x) (ρ ≫ y) := by
    rw [hv _ ρ.left z J hJ, val_mul hJ, val_inv, hv₁ T' ρ z J hJ, hv₂ T' ρ z J hJ, h1]; rfl
  rw [← e, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)]
  exact gm_res ρ.left z le trivial _

def weilUnit (c : CubicalStr G L) (N : ℕ) (T : Over S) (x y : T ⟶ G) (hx : x ^ N = 1) (hy : y ^ N = 1) :
    (Γ(T.left, ⊤))ˣ := (exists_weilUnit c N x y hx hy).choose

theorem gm_weilUnit (c : CubicalStr G L) (N : ℕ) {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1)
    {T' : Over S} (ρ : T' ⟶ T) (z : T'.left) {J} (hJ : Good L.L z J) :
    gm ρ.left z ⊤ (weilUnit c N T x y hx hy) = wq (cubV c z J) N (ρ ≫ x) (ρ ≫ y) :=
  (exists_weilUnit c N x y hx hy).choose_spec T' ρ z J hJ

theorem gm_id_weilUnit (c : CubicalStr G L) (N : ℕ) {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (z : T.left) {J} (hJ : Good L.L z J) :
    gm (𝟙 T.left) z ⊤ (weilUnit c N T x y hx hy) = wq (cubV c z J) N x y := by
  have := gm_weilUnit c N hx hy (𝟙 T) z hJ
  rwa [Category.id_comp, Category.id_comp] at this

omit [IsCommMonObj G] in
theorem exists_good_at (L : RigLB G) {Z : Scheme.{0}} (z : Z) : ∃ J : (Z ⟶ G.left) → L.L.ι, Good L.L z J := by
  choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
  exact ⟨I, hI⟩

theorem weilUnit_comp' (c : CubicalStr G L) (N : ℕ) {T T' : Over S} (r : T' ⟶ T) {x y : T ⟶ G} (hx : x ^ N = 1)
    (hy : y ^ N = 1) (hx' : (r ≫ x) ^ N = 1) (hy' : (r ≫ y) ^ N = 1) :
    weilUnit c N T' (r ≫ x) (r ≫ y) hx' hy' = pullU r.left ⊤ (weilUnit c N T x y hx hy) := by
  refine unit_ext (V := ⊤) fun z _ => ?_
  obtain ⟨J, hJ⟩ := exists_good_at L z
  rw [gm_id_weilUnit c N hx' hy' z hJ, ← gm_weilUnit c N hx hy r z hJ]
  exact ((gm_pull (𝟙 _) r.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem weilUnit_comp (c : CubicalStr G L) (N : ℕ) {T T' : Over S} (r : T' ⟶ T) {x y : T ⟶ G} (hx : x ^ N = 1)
    (hy : y ^ N = 1) (hx' : (r ≫ x) ^ N = 1) (hy' : (r ≫ y) ^ N = 1) :
    (weilUnit c N T' (r ≫ x) (r ≫ y) hx' hy').val = r.left.appTop.hom (weilUnit c N T x y hx hy).val :=
  congrArg Units.val (weilUnit_comp' c N r hx hy hx' hy')

theorem exists_gen_of_subsingleton {X Y : Scheme.{0}} [Subsingleton Y] {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y₀ : Y) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen := by
  choose j₀ hj₀ using fun k => exists_chart hM (φ k y₀)
  have m : ∀ y : Y, y ∈ LB.wchart M φ j₀ := fun y => by
    rw [Subsingleton.elim y y₀]; exact Set.mem_iInter.2 hj₀
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j => le_inf le_rfl fun y _ => m y
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j, y ∈ LB.wchart M φ j → gm (𝟙 Y) y (LB.wchart M φ j) (res (le j) ((LB.LinComb M φ ε).g j j₀)) =
      trF φ ε (𝟙 Y) y j j₀ := fun j hj => (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb M φ ε (𝟙 Y) y j j₀ hj (m y))
  exact (v j hj).trans ((trF_trans hM φ ε (𝟙 Y) y hj hj' (m y)).symm.trans (congrArg _ (v j' hj').symm))

theorem exists_theta (c : CubicalStr G L) (N : ℕ) {T : Over S} [Subsingleton T.left] (z : T.left) (x : T ⟶ G)
    (hx : x ^ N = 1) : ∃ θ : ThetaGrp G L.L N T, θ.pt = x ∧ ∀ J, Good L.L z J → ∃ κ, ∀ y : T ⟶ G,
      val (L := L.L) (φ := ![(snd T G).left, (translPt G θ.pt).left]) (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ
        (lift (𝟙 T) y).left z J = κ * cubN (cubV c z J) N 1 x y := by
  obtain ⟨u, hu⟩ := exists_gen_of_subsingleton L.isLB (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-(N : ℤ), (N : ℤ)] z
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_cubN c (1 : T ⊗ G ⟶ G) (fst T G ≫ x) (snd T G) N
  have hm : (fst T G ≫ x) ^ N = 1 := (map_pow (preHom (fst T G)) x N).symm.trans
    ((congrArg (preHom (fst T G)) hx).trans (map_one _))
  have h1 : fst T G ≫ (1 : T ⟶ G) = 1 := map_one (preHom (fst T G))
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB (φ' := ![(snd T G).left, (translPt G x).left]) (ε' := ![(N : ℤ), -(N : ℤ)])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_two (fst T G) x 1 _ _ h) rfl).trans ?_)
      simp only [Sum.elim_inr, hm, h1, _root_.one_mul, translPt_eq]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u (fst T G).left) t₁)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) ht₁)
  refine ⟨⟨x, t, ht⟩, rfl, fun J hJ => ⟨val u (𝟙 T : T ⟶ T).left z J, fun y => ?_⟩⟩
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_)
    ((hv₁ T (lift (𝟙 T) y) z J hJ).trans ?_)))
  · rw [← Over.comp_left, lift_fst]
  · rw [lift_fst_assoc, lift_snd, Category.id_comp, show lift (𝟙 T) y ≫ (1 : T ⊗ G ⟶ G) = 1 from map_one (preHom _)]

theorem eq_weilUnit_of_comm (c : CubicalStr G L) (N : ℕ) {T : Over S} [Subsingleton T.left] {x y : T ⟶ G}
    (hx : x ^ N = 1) (hy : y ^ N = 1) (a : Γ(T.left, ⊤)ˣ)
    (h : ∀ θx θy : ThetaGrp G L.L N T, θx.pt = x → θy.pt = y → CommIsOf G L.L N θx θy a) :
    weilUnit c N T x y hx hy = a := by
  refine unit_ext fun z _ => ?_
  obtain ⟨J, hJ⟩ := exists_good_at L z
  obtain ⟨θx, rfl, vx⟩ := exists_theta c N z x hx
  obtain ⟨θy, rfl, vy⟩ := exists_theta c N z y hy
  obtain ⟨κx, vx⟩ := vx J hJ
  obtain ⟨κy, vy⟩ := vy J hJ
  have e := val_corr hJ (h θx θy rfl rfl) (lift (𝟙 T) (1 : T ⟶ G)).left
  have tr : ∀ w : T ⟶ G, (lift (𝟙 T) (1 : T ⟶ G)).left ≫ (translT G w).left = (lift (𝟙 T) w).left := fun w => by
    rw [← Over.comp_left, lift_transl, Category.id_comp, _root_.mul_one]
  have vc : val (constGen G L.L a) (lift (𝟙 T) (1 : T ⟶ G)).left z J = gm (𝟙 T.left) z ⊤ a := by
    rw [H1.val_constGen, ← Over.comp_left, lift_fst]; rfl
  have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vx 1) (((val_pull hJ _ _ _).trans
    (congrArg (val _ · z J) (tr _))).trans (vy _)))).symm.trans (e.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vy 1) (((val_pull hJ _ _ _).trans
        (congrArg (val _ · z J) (tr _))).trans (vx _)))) vc)))
  rw [(isCub_cubV c hJ).N_one, (isCub_cubV c hJ).N_one] at e'
  rw [gm_id_weilUnit c N hx hy z hJ, wq]
  apply Additive.ofMul.injective
  have b := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at b ⊢
  linear_combination (norm := abel) b

theorem weilUnit_eq_of_weilIs (c : CubicalStr G L) (N : ℕ) {T : Over S} [Subsingleton T.left] {x y : T ⟶ G}
    (hx : x ^ N = 1) (hy : y ^ N = 1) (a : Γ(T.left, ⊤)ˣ) (h : WeilIs G L.L N x y a) :
    weilUnit c N T x y hx hy = a := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hp, -, hV⟩ := h p
  have hp' : ∀ {w : T ⟶ G}, w ^ N = 1 → (overResι V ≫ w) ^ N = 1 := fun {w} hw =>
    (map_pow (preHom (overResι V)) w N).symm.trans ((congrArg (preHom (overResι V)) hw).trans (map_one _))
  have : Subsingleton (overRes V).left := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have e := eq_weilUnit_of_comm c N (hp' hx) (hp' hy) (unitRes V a) hV
  rw [weilUnit_comp' c N (overResι V) hx hy] at e
  have e₂ : gm V.ι ⟨p, hp⟩ ⊤ (weilUnit c N T x y hx hy) = gm V.ι ⟨p, hp⟩ ⊤ a := by
    have := congrArg (gm (𝟙 V.toScheme) ⟨p, hp⟩ ⊤) e
    have g := fun b => (gm_pull (𝟙 V.toScheme) V.ι ⟨p, hp⟩ ⊤ trivial b).trans (by rw [Category.id_comp])
    exact (g _).symm.trans (this.trans (g _))
  apply Units.ext
  have hi : IsIso (V.ι.stalkMap (show V.toScheme from ⟨p, hp⟩)) := inferInstance
  apply (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap (show V.toScheme from ⟨p, hp⟩))).1
  have s : ∀ b : Γ(T.left, ⊤)ˣ, (V.ι.stalkMap ⟨p, hp⟩).hom (gm (𝟙 T.left) p ⊤ b).val = (gm V.ι ⟨p, hp⟩ ⊤ b).val := fun b => by
    rw [gm_val _ p ⊤ trivial, gm_val V.ι ⟨p, hp⟩ ⊤ trivial]
    exact Scheme.Hom.germ_stalkMap_apply V.ι ⊤ ⟨p, hp⟩ trivial b.val
  exact (s _).trans ((congrArg Units.val e₂).trans (s _).symm)

end PositivityTheory.HtPt.Weilfun
