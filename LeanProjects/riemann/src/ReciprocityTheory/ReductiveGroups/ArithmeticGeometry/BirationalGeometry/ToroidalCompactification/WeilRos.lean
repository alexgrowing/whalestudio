import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfTrivial

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_local_gen {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (LB.LinComb M (fun k => V.ι ≫ φ k) ε), t.IsGen := by
  choose j₀ hj using fun k => exists_chart hM (φ k y)
  refine ⟨LB.wchart M φ j₀, Set.mem_iInter.2 hj, ?_⟩
  have all : ∀ w : (LB.wchart M φ j₀).toScheme, w ∈ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun w =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 w.2 k
  have le : ∀ j, LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ≤ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ⊓
      LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun j w hw => ⟨hw, all w⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) ε).g j j₀)⟩,
    isGen_of_gm _ fun w j j' h h' => ?_⟩
  exact ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j j₀ h (all w))).trans
    ((trF_trans hM _ ε (𝟙 _) w h h' (all w)).symm.trans (congrArg _
      ((gm_res _ w (le j') h' _).trans (gm_linComb M _ ε (𝟙 _) w j' j₀ h' (all w))).symm))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

include c in
theorem exists_theta {k : ℕ} {T : Over S} {x : T ⟶ A} (hx : x ^ k = 1) {K : Type} [Fintype K] {φ : K → (T.left ⟶ A.left)}
    {ε : K → ℤ} (v : LB.Gen (LB.LinComb L.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (1 : T ⟶ A).left ^ (k : ℤ) * h x.left ^ (-(k : ℤ))) : ∃ θ : ThetaGrp A L.L k T, θ.pt = x := by
  obtain ⟨t, ht, -⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ x) (snd T A) k
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      have p := hF U fun q => h ((fst T A).left ≫ q)
      rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one] at p
      refine (prod_sum₂ (K := K) (K' := Fin 8) (U := U) _ p (Fin.prod_univ_eight _)).trans ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← MonObj.comp_pow, hx, MonObj.comp_one, _root_.one_mul (1 : T ⊗ A ⟶ A), _root_.one_mul (snd T A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ v (fst T A).left) t)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hv _) ht)
  exact ⟨⟨x, u, hu⟩, rfl⟩

theorem exists_weil {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ w : Γ(T.left, ⊤)ˣ,
    ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹ := by
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : T ⟶ A) y x k
  obtain ⟨t', ht', vt'⟩ := exists_cubN c (1 : T ⟶ A) x y k
  obtain ⟨u, -, vu⟩ := exists_gen L.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 8) (K' := Fin 8) (U := U) _ (Fin.prod_univ_eight _)
        (prod_neg _ _ (Fin.prod_univ_eight _))).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inr, Sum.elim_inl, Matrix.cons_val]
      rw [hx, hy, _root_.one_mul (1 : T ⟶ A), mul_comm y x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (LB.mulGen L.L _ _ _ _ t (LB.invGen L.L _ _ t')) (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L.L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (u.s PEmpty.elim), fun T' σ z J hJ => (gm_res σ.left z le trivial _).trans
    ((val_of u σ.left z J PEmpty.elim fun k => k.elim).symm.trans ?_)⟩
  rw [vu _ _ z J hJ, val_mul hJ, val_inv, vt _ σ z J hJ, vt' _ σ z J hJ, MonObj.comp_one]

def thG {k : ℕ} {T : Over S} (W : ThetaGrp A L.L k T) :
    LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (translPt A W.pt).left] ![(k : ℤ), -(k : ℤ)]) := W.φ

theorem thG_mul (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (W W' : ThetaGrp A L.L k T)
    (hW : W.pt ^ k = 1) (hW' : W'.pt ^ k = 1) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J} (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG W) (LB.pullGen L.L _ _ (thG W') (translT A W.pt).left)) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y *
        (val (thG W') (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W'.pt) ((σ ≫ W.pt) * y)) := by
  have v : ∀ (W : ThetaGrp A L.L k T), W.pt ^ k = 1 → ∀ y : T' ⟶ A, val (thG W) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y := fun W hW y =>
    val_theta c hG hA hW (thG W) W.isGen (fun V _ h => by
      rw [Fin.prod_univ_two]
      show h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ)) = _
      rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl) σ y hJ
  rw [val_mul hJ, val_pull hJ, ← Over.comp_left, lift_transl, v W hW y, v W' hW' (_ * y)]

theorem comm_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (θ θ' : ThetaGrp A L.L k T)
    (hx : θ.pt ^ k = 1) (hy : θ'.pt ^ k = 1) (e : Γ(T.left, ⊤)ˣ) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J}
    (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG θ) (LB.pullGen L.L _ _ (thG θ') (translT A θ.pt).left)) (lift σ y).left z J =
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (thG θ') (LB.pullGen L.L _ _ (thG θ) (translT A θ'.pt).left))
        (constGen A L.L e)) (lift σ y).left z J ↔ gm σ.left z ⊤ e =
      cubN (cubV c z J) k 1 (σ ≫ θ'.pt) (σ ≫ θ.pt) * (cubN (cubV c z J) k 1 (σ ≫ θ.pt) (σ ≫ θ'.pt))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have pk : ∀ {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
  have hm : (lift σ y).left z ∈ LB.wchart L.L (PEmpty.elim : PEmpty → ((T ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  have vc : val (constGen A L.L e) (lift σ y).left z J = gm σ.left z ⊤ e := by
    rw [val_of _ _ z J PEmpty.elim fun k => k.elim]
    refine (gm_res (lift σ y).left z le_top hm _).trans ((gm_pull (lift σ y).left (fst T A).left z ⊤ trivial e).trans ?_)
    rw [← Over.comp_left, lift_fst]
  rw [thG_mul c hG hA θ θ' hx hy σ y hJ, val_mul hJ, thG_mul c hG hA θ' θ hy hx σ y hJ, vc]
  have a₁ := cubN_right C (pk hx) (σ ≫ θ'.pt) y
  have a₂ := cubN_right C (pk hy) (σ ≫ θ.pt) y
  rw [C.s01] at a₂
  have E := fun {p q : (T'.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have b₁ := E a₁
  have b₂ := E a₂
  simp only [ofMul_mul] at b₁ b₂
  refine ⟨fun h => Additive.ofMul.injective ?_, fun h => Additive.ofMul.injective ?_⟩
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'

theorem weilIs_iff (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1)
    (hy : y ^ k = 1) {w : Γ(T.left, ⊤)ˣ} (hw : ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs A L.L k x y e ↔ e = w := by
  have pk : ∀ {T' : Over S} (σ : T' ⟶ T) {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun σ _ h => by
    rw [← MonObj.comp_pow, h, MonObj.comp_one]
  constructor
  · refine fun h => unit_ext fun p _ => ?_
    obtain ⟨V, hV, ⟨θ, θ', h₁, h₂⟩, hc⟩ := h p
    let z : (overRes V).left := ⟨p, hV⟩
    choose J hJ using fun ψ : (overRes V).left ⟶ A.left => exists_chart L.isLB (ψ z)
    have e₁ := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes V e) (𝟙 _) 1 hJ).1
      (val_corr hJ (hc θ θ' h₁ h₂) _)
    rw [Category.id_comp, Category.id_comp, h₁, h₂, ← hw _ (overResι V) z J hJ] at e₁
    exact gm_inj V.ι z (U := ⊤) (U' := ⊤) trivial trivial (((gm_pull (𝟙 _) V.ι z ⊤ trivial e).trans (by rw [Category.id_comp])).symm.trans e₁)
  · rintro rfl p
    obtain ⟨V₁, hV₁, v₁, hv₁⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![(k : ℤ), -(k : ℤ)] p
    obtain ⟨V₂, hV₂, v₂, hv₂⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(k : ℤ), -(k : ℤ)] p
    have ex : ∀ (W : T.left.Opens) (le : V₁ ⊓ V₂ ≤ W) (q : T ⟶ A), q ^ k = 1 → ∀ v : LB.Gen (LB.LinComb L.L
        (fun i => W.ι ≫ (![(1 : T ⟶ A).left, q.left] : Fin 2 → _) i) ![(k : ℤ), -(k : ℤ)]), v.IsGen →
        ∃ θ : ThetaGrp A L.L k (overRes (V₁ ⊓ V₂)), θ.pt = overResι (V₁ ⊓ V₂) ≫ q := fun W le q hq v hv =>
      exists_theta c (pk _ hq) (LB.pullGen L.L _ _ v (T.left.homOfLE le)) (pullGen_isGen _ _ _ _ hv _) fun U _ h => by
        rw [Fin.prod_univ_two, ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, ← MonObj.comp_one (overResι (V₁ ⊓ V₂))]
        rfl
    obtain ⟨θ₁, e₁⟩ := ex V₁ inf_le_left x hx v₁ hv₁
    obtain ⟨θ₂, e₂⟩ := ex V₂ inf_le_right y hy v₂ hv₂
    refine ⟨V₁ ⊓ V₂, ⟨hV₁, hV₂⟩, ⟨θ₁, θ₂, e₁, e₂⟩, fun θ θ' h₁ h₂ => corr_of_val L.isLB fun z J hJ => ?_⟩
    have i₁ : (lift (fst (overRes (V₁ ⊓ V₂)) A) (snd _ A)).left = 𝟙 _ := by
      rw [lift_fst_snd]; rfl
    have key := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes (V₁ ⊓ V₂) e) (fst _ A) (snd _ A) hJ).2 (by
      rw [h₁, h₂, ← Category.assoc, ← Category.assoc, ← hw _ (fst _ A ≫ overResι (V₁ ⊓ V₂)) z J hJ]
      exact gm_pull _ (V₁ ⊓ V₂).ι z ⊤ trivial e)
    rw [i₁] at key
    exact key

theorem ros_pair (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ u (zero2 A)) (LB.oneGen L.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L.L z J) {k : ℕ} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN (cubV c z J) k 1 y (x ≫ f) * (cubN (cubV c z J) k 1 (x ≫ f) y)⁻¹ =
      cubN (cubV c z J) k 1 (y ≫ g) x * (cubN (cubV c z J) k 1 x (y ≫ g))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have ra := fun x x' y => ros_add c hG hA f g u hu n hJ x x' y
  have u₁ : val₂ u z J (1 : T ⟶ A) y = 1 := by
    have e := (ra 1 1 y).1
    rw [_root_.mul_one, MonObj.one_comp f, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : val₂ u z J x (1 : T ⟶ A) = 1 := by
    have e := (ra 1 1 x).2
    rw [_root_.mul_one, MonObj.one_comp g, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a : ∀ j, val₂ u z J (x ^ j) y * cubN (cubV c z J) j 1 x (y ≫ g) =
      cubN (cubV c z J) j 1 (x ≫ f) y * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₁]
    | succ j ih =>
      have e := (ra (x ^ j) x y).1
      rw [MonObj.pow_comp] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have b : ∀ j, val₂ u z J x (y ^ j) * cubN (cubV c z J) j 1 (y ≫ g) x =
      cubN (cubV c z J) j 1 y (x ≫ f) * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₂]
    | succ j ih =>
      have e := (ra (y ^ j) y x).2
      rw [MonObj.pow_comp, C.s01 x, C.s12 _ x, C.s01 (x ≫ f), C.s12 _ (x ≫ f)] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have a' := a k
  have b' := b k
  rw [hx, u₁, _root_.one_mul] at a'
  rw [hy, u₂, _root_.one_mul] at b'
  rw [a', b', mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

theorem weilRosati (hG : GlobalFnsSt) (hC : CubeSt) : WeilRosatiSt := by
  intro S _ P O _ _ o k T x y a e hx hy
  have := P.isAb.comm
  have := o.hom a
  have := o.hom (star a)
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hC S P ⟨P.L, r, P.isLB, hr⟩ rfl
  obtain ⟨u, hu, n⟩ := exists_ros hG P.isAb P.isLB _ _ (o.rosati a)
  have hx' : (x ≫ o.act a) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy' : (y ≫ o.act (star a)) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨w, hw⟩ := exists_weil c hx' hy
  refine (weilIs_iff c hG P.isAb hx' hy hw e).trans (weilIs_iff c hG P.isAb hx hy' (fun T' σ z J hJ => ?_) e).symm
  rw [hw T' σ z J hJ, ← Category.assoc, ← Category.assoc]
  exact ros_pair c hG P.isAb _ _ u hu n hJ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
