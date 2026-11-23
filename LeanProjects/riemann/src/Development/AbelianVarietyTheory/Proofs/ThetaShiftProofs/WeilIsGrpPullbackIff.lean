import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

namespace WeilCube

theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (i : K → L.ι) (h : ∀ y, y ∈ LB.wchart L φ i) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ i := fun j => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j i)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j i)) =
      trF φ ε (𝟙 Y) y j i := fun j hj => (gm_res _ y _ hj _).trans (gm_linComb L φ ε _ y j i hj (h y))
  refine ((gm_res _ y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h y)).symm

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem exists_gen_torsion {T : Over S} (k : ℕ) (x y : T ⟶ A) (hx : x ^ k = 1) :
    ∃ t : LB.Gen (LB.LinComb Lr.L (K := Fin 4) ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left] ![-k, k, k, -k]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good Lr.L z J →
        val t ρ.left z J = cubN (cubV c z J) k 1 (ρ ≫ x) (ρ ≫ y) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⟶ A) x y k
  obtain ⟨t', ht', hv'⟩ := exists_gen Lr.isLB (φ' := ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left])
    (ε' := ![-k, k, k, -k]) (fun U _ h => by
      rw [hx]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel) t ht
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((hv T' ρ z J hJ).trans ?_)⟩
  rw [MonObj.comp_one]

def IsRatio (k : ℕ) {T : Over S} (x y : T ⟶ A) (e : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good Lr.L z J →
    gm ρ.left z ⊤ e * cubN (cubV c z J) k 1 (ρ ≫ x) (ρ ≫ y) = cubN (cubV c z J) k 1 (ρ ≫ y) (ρ ≫ x)

theorem exists_isRatio (k : ℕ) {T : Over S} (x y : T ⟶ A) (hx : x ^ k = 1) (hy : y ^ k = 1) :
    ∃ e, IsRatio c k x y e := by
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen_torsion c k x y hx
  obtain ⟨t₂, h₂, v₂⟩ := exists_gen_torsion c k y x hy
  obtain ⟨t, -, hv⟩ := exists_gen Lr.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      rw [mul_comm y x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
    (LB.mulGen Lr.L _ _ _ _ t₂ (LB.invGen Lr.L _ _ t₁))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₂ (DVR.invGen_isGen _ _ _ _ h₁))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart Lr.L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  have e := hv _ ρ.left z J hJ
  rw [val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)] at e
  exact (congrArg (· * _) ((gm_res ρ.left z le trivial _).trans e)).trans (inv_mul_cancel_right _ _)

theorem IsRatio.comp {k : ℕ} {T T' : Over S} {x y : T ⟶ A} {e : Γ(T.left, ⊤)ˣ} (h : IsRatio c k x y e) (σ : T' ⟶ T) :
    IsRatio c k (σ ≫ x) (σ ≫ y) (Units.map σ.left.appTop.hom.toMonoidHom e) := by
  intro T'' ρ z J hJ
  have := h T'' (ρ ≫ σ) z J hJ
  rw [Category.assoc, Category.assoc, Over.comp_left, ← gm_pull ρ.left σ.left z ⊤ trivial] at this
  exact this

omit [IsCommMonObj A] in
theorem surj_fst (hG : GlobalFnsSt) [IsCommMonObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (lift (snd T A) (fst T A)).left ≫ (snd A T).left := by rw [← Over.comp_left, lift_snd]
  rw [e]
  refine surj_comp (fun a => ⟨(lift (snd A T) (fst A T)).left.appTop.hom a, ?_⟩) (surj_snd hG hA T)
  have : (lift (snd T A) (fst T A)).left ≫ (lift (snd A T) (fst A T)).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_lift, lift_snd, lift_fst, lift_fst_snd, Over.id_left]
  have h2 := congrArg (fun q => q.appTop.hom a) this
  exact h2.trans (congrArg (fun q => q.hom a) (Scheme.Hom.id_appTop))

theorem val_theta (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (θ : ThetaGrp A Lr.L k T)
    (hx : θ.pt ^ k = 1) {T' : Over S} (σ : T' ⟶ T ⊗ A) (z : T'.left) (J) (hJ : Good Lr.L z J) :
    val θ.φ σ.left z J = cubN (cubV c z J) k 1 (σ ≫ fst T A ≫ θ.pt) (σ ≫ snd T A) *
      val θ.φ (lift (σ ≫ fst T A) (1 : T' ⟶ A)).left z J := by
  have hx' : (fst T A ≫ θ.pt) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, hv⟩ := exists_gen_torsion c k (fst T A ≫ θ.pt) (snd T A) hx'
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) 1
  have hn : ∀ {T'' : Over S} (τ : T'' ⟶ T ⊗ A), τ ≫ n = lift (τ ≫ fst T A) 1 := fun τ => by
    rw [comp_lift, MonObj.comp_one]
  have ev : ∀ {T'' : Over S} (τ : T'' ⟶ T ⊗ A) (z : T''.left) (J), Good Lr.L z J →
      val (LB.mulGen Lr.L _ _ _ _ t (LB.pullGen Lr.L _ _ θ.φ n.left)) τ.left z J =
        cubN (cubV c z J) k 1 (τ ≫ fst T A ≫ θ.pt) (τ ≫ snd T A) *
          val θ.φ (lift (τ ≫ fst T A) (1 : _ ⟶ A)).left z J := fun τ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ τ z J hJ) ((val_pull hJ _ _ _).trans (by
      rw [← Over.comp_left, hn])))
  let e : T ⟶ T ⊗ A := lift (𝟙 T) 1
  have n₀ : n.left ≫ (snd T A).left = (1 : T ⊗ A ⟶ A).left := by rw [← Over.comp_left, lift_snd]
  have n₁ : n.left ≫ (translPt A θ.pt).left = (fst T A ≫ θ.pt).left := by
    rw [← Over.comp_left]
    congr 1
    show n ≫ ((fst T A ≫ θ.pt) * snd T A) = _
    rw [MonObj.comp_mul, lift_snd, _root_.mul_one, ← Category.assoc, lift_fst]
  refine (gen_unique' Lr.isLB (fun U _ h => ?_) (fst T A).left e.left (by rw [← Over.comp_left, lift_fst, Over.id_left])
    (surj_fst hG hA T) θ.isGen (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ θ.isGen n.left))
    (fun y I hI => ?_) _ σ.left z J hJ).trans (ev σ z J hJ)
  · refine (Fintype.prod_sum_type _).trans ?_
    have e₁ : ((fst T A ≫ θ.pt) * snd T A).left = (translPt A θ.pt).left := rfl
    simp only [Fin.prod_univ_succ, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, n₀, n₁, e₁,
      Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · refine Eq.trans ?_ (ev e y I hI).symm
    rw [lift_snd, lift_fst, (isCub_cubV c hI).N_one, _root_.one_mul]

theorem comm_alg {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) {k : ℕ} {a b : G}
    (ha : a ^ k = 1) (hb : b ^ k = 1) (s : G) (p q e : U) (he : e * cubN θ k 1 a b = cubN θ k 1 b a) :
    cubN θ k 1 a s * p * (cubN θ k 1 b (a * s) * q) = cubN θ k 1 b s * q * (cubN θ k 1 a (b * s) * p) * e := by
  have e₁ := h.N_add k 1 a b s
  have e₂ := h.N_add k 1 b a s
  rw [ha, _root_.one_mul, h.face] at e₁
  rw [hb, _root_.one_mul, h.face, h.s01 b a] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul he
  simp only [ofMul_mul, ofMul_one] at *
  linear_combination (norm := abel) a₂ - a₁ - a₃

theorem commIsOf_of_isRatio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S}
    (θx θy : ThetaGrp A Lr.L k T) (hx : θx.pt ^ k = 1) (hy : θy.pt ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : IsRatio c k θx.pt θy.pt e) : CommIsOf A Lr.L k θx θy e := by
  refine corr_of_val Lr.isLB fun y J hJ => ?_
  have a₁ := val_theta c hG hA θx hx (𝟙 _) y J hJ
  have a₂ := val_theta c hG hA θy hy (translT A θx.pt) y J hJ
  have a₃ := val_theta c hG hA θy hy (𝟙 _) y J hJ
  have a₄ := val_theta c hG hA θx hx (translT A θy.pt) y J hJ
  have tf : ∀ x : T ⟶ A, translT A x ≫ fst T A = fst T A := fun x => lift_fst _ _
  have ts : ∀ x : T ⟶ A, translT A x ≫ snd T A = (fst T A ≫ x) * snd T A := fun x => lift_snd _ _
  rw [Category.id_comp, Category.id_comp, Category.id_comp, Over.id_left] at a₁ a₃
  rw [← Category.assoc, tf, ts] at a₂ a₄
  refine ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg (val θy.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))) (val_constGen _ _ _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp, a₁, a₂, a₃, a₄]
  exact comm_alg (isCub_cubV c hJ) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) _ _ _ _ (he _ (fst T A) y J hJ)

include c in

theorem exists_theta {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) (i j : Lr.L.ι)
    (hi : ∀ p, x.left p ∈ Lr.L.U i) (hj : ∀ p, (1 : T ⟶ A).left p ∈ Lr.L.U j) :
    ∃ θ : ThetaGrp A Lr.L k T, θ.pt = x := by
  have hx' : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, -⟩ := exists_gen_torsion c k (fst T A ≫ x) (snd T A) hx'
  have o : (1 : T ⊗ A ⟶ A) = fst T A ≫ 1 := (MonObj.comp_one _).symm
  obtain ⟨s, hs⟩ := exists_gen_of_chart Lr.isLB (K := Fin 2) ![(fst T A ≫ x).left, (1 : T ⊗ A ⟶ A).left] ![-k, k] ![i, j]
    (fun y => Set.mem_iInter.2 fun a => by
      fin_cases a
      · exact hi _
      · show (1 : T ⊗ A ⟶ A).left y ∈ Lr.L.U j
        rw [o]; exact hj _)
  obtain ⟨u, hu, -⟩ := exists_gen Lr.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![k, -k])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : ((fst T A ≫ x) * snd T A).left = (translPt A x).left := rfl
      simp only [Fin.prod_univ_succ, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁,
        Fin.prod_univ_zero]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen Lr.L _ _ _ _ t s) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hs)
  exact ⟨⟨x, u, hu⟩, rfl⟩

theorem germ_eq_of_unitRes {T : Over S} {V : T.left.Opens} {p : T.left} (hp : p ∈ V) {e e' : Γ(T.left, ⊤)ˣ}
    (h : unitRes V e = unitRes V e') : gm (𝟙 _) p ⊤ e = gm (𝟙 _) p ⊤ e' := by
  have v : ∀ a : Γ(T.left, ⊤)ˣ, gm V.ι (⟨p, hp⟩ : V.toScheme) ⊤ a =
      gm (𝟙 V.toScheme) (⟨p, hp⟩ : V.toScheme) ⊤ (unitRes V a) := fun a =>
    (congrArg (fun q => gm q (⟨p, hp⟩ : V.toScheme) ⊤ a) (Category.id_comp V.ι).symm).trans
      (gm_pull (𝟙 _) V.ι ⟨p, hp⟩ ⊤ trivial a).symm
  exact gm_inj V.ι ⟨p, hp⟩ (U := ⊤) (U' := ⊤) trivial trivial ((v e).trans ((congrArg _ h).trans (v e').symm))

theorem weilIs_iff (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1)
    (hy : y ^ k = 1) {e₀ : Γ(T.left, ⊤)ˣ} (he : IsRatio c k x y e₀) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs A Lr.L k x y e ↔ e = e₀ := by
  have rp : ∀ (V : T.left.Opens) (w : T ⟶ A), w ^ k = 1 → (overResι V ≫ w) ^ k = 1 := fun V w hw => by
    rw [← MonObj.comp_pow, hw, MonObj.comp_one]
  have all : ∀ (V : T.left.Opens) (θx θy : ThetaGrp A Lr.L k (overRes V)), θx.pt = overResι V ≫ x →
      θy.pt = overResι V ≫ y → CommIsOf A Lr.L k θx θy (unitRes V e₀) := fun V θx θy h₁ h₂ =>
    commIsOf_of_isRatio c hG hA θx θy (h₁ ▸ rp V x hx) (h₂ ▸ rp V y hy) (by
      rw [h₁, h₂]; exact he.comp c (overResι V))
  constructor
  · intro h
    refine unit_ext fun p _ => ?_
    obtain ⟨V, hp, ⟨θx, θy, h₁, h₂⟩, H⟩ := h p
    exact germ_eq_of_unitRes hp (commIsOf_unique Lr.isLB θx θy _ _ (H θx θy h₁ h₂) (all V θx θy h₁ h₂))
  · rintro rfl p
    obtain ⟨i, hi⟩ := exists_chart Lr.isLB (x.left p)
    obtain ⟨i', hi'⟩ := exists_chart Lr.isLB (y.left p)
    obtain ⟨j, hj⟩ := exists_chart Lr.isLB ((1 : T ⟶ A).left p)
    let V : T.left.Opens := x.left ⁻¹ᵁ Lr.L.U i ⊓ y.left ⁻¹ᵁ Lr.L.U i' ⊓ (1 : T ⟶ A).left ⁻¹ᵁ Lr.L.U j
    have o : ∀ q, (1 : overRes V ⟶ A).left q ∈ Lr.L.U j := fun q => by
      rw [← MonObj.comp_one (overResι V)]; exact q.2.2
    obtain ⟨θx, h₁⟩ := exists_theta c (overResι V ≫ x) (rp V x hx) i j (fun q => q.2.1.1) o
    obtain ⟨θy, h₂⟩ := exists_theta c (overResι V ≫ y) (rp V y hy) i' j (fun q => q.2.1.2) o
    exact ⟨V, ⟨⟨hi, hi'⟩, hj⟩, ⟨θx, θy, h₁, h₂⟩, all V⟩

theorem cubN_rosati (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A Lr.L f g) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) (z : T.left) (J)
    (hJ : Good Lr.L z J) : ∃ u, cubN (cubV c z J) k 1 x (y ≫ g) = cubN (cubV c z J) k 1 (x ≫ f) y * u ∧
      cubN (cubV c z J) k 1 (y ≫ g) x = cubN (cubV c z J) k 1 y (x ≫ f) * u := by
  obtain ⟨u, hu, h₀⟩ := exists_ros hG hA Lr.isLB f g h
  have C := isCub_cubV c hJ
  have first : ∀ n : ℕ, val₂ u z J (x ^ n) y * cubN (cubV c z J) n 1 x (y ≫ g) =
      val₂ u z J 1 y * (cubN (cubV c z J) n 1 (x ≫ f) y * val₂ u z J x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := (ros_add c hG hA f g u hu h₀ hJ (x ^ n) x y).1
      rw [MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, val₂ u z J x (y ^ n) * cubN (cubV c z J) n 1 (y ≫ g) x =
      val₂ u z J x 1 * (cubN (cubV c z J) n 1 y (x ≫ f) * val₂ u z J x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := (ros_add c hG hA f g u hu h₀ hJ (y ^ n) y x).2
      rw [MonObj.pow_comp, C.s01 x, C.s12 _ x, C.s01 (x ≫ f), C.s12 _ (x ≫ f)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨_, mul_left_cancel a, mul_left_cancel b⟩

theorem IsRatio.rosati (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A Lr.L f g) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1)
    {e : Γ(T.left, ⊤)ˣ} (he : IsRatio c k (x ≫ f) y e) : IsRatio c k x (y ≫ g) e := by
  intro T' ρ z J hJ
  obtain ⟨u, h₁, h₂⟩ := cubN_rosati c hG hA f g h (x := ρ ≫ x) (y := ρ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) z J hJ
  have := he T' ρ z J hJ
  rw [← Category.assoc] at this ⊢
  rw [h₁, h₂, ← this, _root_.mul_assoc]

include c in

theorem weilIs_rosati (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A Lr.L f g) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1)
    (e : Γ(T.left, ⊤)ˣ) : WeilIs A Lr.L k (x ≫ f) y e ↔ WeilIs A Lr.L k x (y ≫ g) e := by
  have hx' : (x ≫ f) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy' : (y ≫ g) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨e₀, he⟩ := exists_isRatio c k (x ≫ f) y hx' hy
  rw [weilIs_iff c hG hA hx' hy he, weilIs_iff c hG hA hx hy' (he.rosati c hG hA f g h hx hy)]

include c in

theorem weilIs_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G]
    {L₀ : LB G.left} (hL₀ : L₀.IsLB) {f : S ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    (w : LB.Iso Lr.L (L₀.pull φ)) (hw : w.IsGen) {k : ℕ} {T : Over S} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) {x₀ y₀ : T₀ ⟶ G}
    (ex : τ ≫ x₀.left = x.left ≫ φ) (ey : τ ≫ y₀.left = y.left ≫ φ) {e₀ : Γ(T₀.left, ⊤)ˣ}
    (H : WeilIs G L₀ k x₀ y₀ e₀) : WeilIs A Lr.L k x y (Units.map τ.appTop.hom.toMonoidHom e₀) := by
  obtain ⟨e, he⟩ := exists_isRatio c k x y hx hy
  refine (weilIs_iff c hG hA hx hy he _).2 (unit_ext fun p _ => ?_)
  obtain ⟨V₀, hpV, ⟨θx₀, θy₀, h₁, h₂⟩, hall⟩ := H (τ p)
  let V : T.left.Opens := τ ⁻¹ᵁ V₀
  have hι : (τ ∣_ V₀) ≫ V₀.ι = V.ι ≫ τ := morphismRestrict_ι τ V₀
  have hτ' : (τ ∣_ V₀) ≫ (overRes V₀).hom = (overRes V).hom ≫ f := by
    show (τ ∣_ V₀) ≫ V₀.ι ≫ T₀.hom = (V.ι ≫ T.hom) ≫ f
    rw [← Category.assoc, hι, Category.assoc, hτ, Category.assoc]
  have mv : ∀ {x : T ⟶ A} {x₀ : T₀ ⟶ G}, τ ≫ x₀.left = x.left ≫ φ →
      (τ ∣_ V₀) ≫ (overResι V₀ ≫ x₀).left = (overResι V ≫ x).left ≫ φ := fun {x x₀} ex => by
    show (τ ∣_ V₀) ≫ V₀.ι ≫ x₀.left = (V.ι ≫ x.left) ≫ φ
    rw [← Category.assoc, hι, Category.assoc, ex, Category.assoc]
  have mvx := mv ex
  have mvy := mv ey
  rw [← h₁] at mvx
  rw [← h₂] at mvy
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move (T := overRes V) (T₀ := overRes V₀) hp (τ ∣_ V₀) hτ' hL₀ Lr.isLB w hw k _
    θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move (T := overRes V) (T₀ := overRes V₀) hp (τ ∣_ V₀) hτ' hL₀ Lr.isLB w hw k _
    θy₀ mvy
  have hm := commIsOf_move (T := overRes V) (T₀ := overRes V₀) hp (τ ∣_ V₀) hτ' hL₀ Lr.isLB w k θx₀ θy₀ θx θy
    (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my (unitRes V₀ e₀)
    (unitRes V (Units.map τ.appTop.hom.toMonoidHom e₀)) (fun Z r z => by
      refine (gm_pull (r ≫ (τ ∣_ V₀)) V₀.ι z ⊤ trivial e₀).trans (Eq.trans ?_
        ((gm_pull r V.ι z ⊤ trivial _).trans (gm_pull (r ≫ V.ι) τ z ⊤ trivial e₀)).symm)
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun q => gm (r ≫ q) z ⊤ e₀) hι) (hall θx₀ θy₀ h₁ h₂)
  have rp : ∀ (a : T ⟶ A), a ^ k = 1 → (overResι V ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  exact germ_eq_of_unitRes (V := V) hpV (commIsOf_unique Lr.isLB θx θy _ _ hm
    (commIsOf_of_isRatio c hG hA θx θy (hθx ▸ rp x hx) (hθy ▸ rp y hy) (by
      rw [hθx, hθy]; exact he.comp c (overResι V))))

end WeilCube

open WeilCube

theorem PolAV_exists_cubical (hC : CubeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) :
    ∃ (r : LB.Gen (P.L.pull (eSec P.A))) (hr : r.IsGen), Nonempty (CubicalStr P.A ⟨P.L, r, P.isLB, hr⟩) := by
  obtain ⟨r, hr⟩ := P.rigid
  exact ⟨r, hr, (hC S P ⟨P.L, r, P.isLB, hr⟩ rfl).1⟩

theorem weilIs_grpPullback_iff (hG : GlobalFnsSt) (hC : CubeSt) {S S' : Scheme.{0}} [IsLocallyNoetherian S]
    [IsLocallyNoetherian S'] (P : PolAV S) (P' : PolAV S') {f : S' ⟶ S} {φ : P'.A.left ⟶ P.A.left}
    (hp : IsGrpPullback P'.A P.A f φ) (w : LB.Iso P'.L (P.L.pull φ)) (hw : w.IsGen) {Z : Scheme.{0}} {t : Z ⟶ S}
    {t' : Z ⟶ S'} (ht : t = t' ≫ f) (k : ℕ) (x y : Over.mk t' ⟶ P'.A) (hx : x ^ k = 1) (hy : y ^ k = 1)
    (x₀ y₀ : Over.mk t ⟶ P.A) (ex : x₀.left = x.left ≫ φ) (ey : y₀.left = y.left ≫ φ) (e : Γ(Z, ⊤)ˣ) :
    WeilIs P.A P.L k x₀ y₀ e ↔ WeilIs P'.A P'.L k x y e := by
  subst ht
  obtain ⟨r, hr, ⟨c⟩⟩ := PolAV_exists_cubical hC P
  obtain ⟨r', hr', ⟨c'⟩⟩ := PolAV_exists_cubical hC P'
  have tor : ∀ (x : Over.mk t' ⟶ P'.A) (x₀ : Over.mk (t' ≫ f) ⟶ P.A), x ^ k = 1 → x₀.left = x.left ≫ φ →
      x₀ ^ k = 1 := fun x x₀ hx ex => by
    have e₁ : x₀ = pushHom hp (Over.mk t') x := Over.OverMorphism.ext ex
    rw [e₁]
    exact (map_pow (pushHom hp (Over.mk t')) x k).symm.trans ((congrArg _ hx).trans (map_one _))
  have pull : ∀ e : Γ(Z, ⊤)ˣ, WeilIs P.A P.L k x₀ y₀ e → WeilIs P'.A P'.L k x y e := fun e H => by
    have := weilIs_pull c' hG P'.isAb P.isLB hp w hw (T := Over.mk t') (T₀ := Over.mk (t' ≫ f)) (𝟙 Z)
      (Category.id_comp _) hx hy ((Category.id_comp _).trans ex) ((Category.id_comp _).trans ey) H
    exact this
  refine ⟨pull e, fun H => ?_⟩
  obtain ⟨e₀, he₀⟩ := exists_isRatio c k x₀ y₀ (tor x x₀ hx ex) (tor y y₀ hy ey)
  obtain ⟨e', he'⟩ := exists_isRatio c' k x y hx hy
  have H₀ := (weilIs_iff c hG P.isAb (tor x x₀ hx ex) (tor y y₀ hy ey) he₀ e₀).2 rfl
  exact (weilIs_iff c hG P.isAb (tor x x₀ hx ex) (tor y y₀ hy ey) he₀ e).2
    (((weilIs_iff c' hG P'.isAb hx hy he' e).1 H).trans ((weilIs_iff c' hG P'.isAb hx hy he' e₀).1 (pull e₀ H₀)).symm)

theorem weilIs_iso_iff (hG : GlobalFnsSt) (hC : CubeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P' P : PolAV S)
    (θ : P'.A ≅ P.A) [IsMonHom θ.hom] (w : LB.Iso P'.L (P.L.pull θ.hom.left)) (hw : w.IsGen) {T : Over S} (k : ℕ)
    (x y : T ⟶ P'.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs P.A P.L k (x ≫ θ.hom) (y ≫ θ.hom) e ↔ WeilIs P'.A P'.L k x y e :=
  weilIs_grpPullback_iff hG hC P P' (isGrpPullback_of_iso θ) w hw (t := T.hom) (t' := T.hom) (Category.comp_id _).symm
    k x y hx hy (x ≫ θ.hom) (y ≫ θ.hom) rfl rfl e

theorem weilIs_rosati_iff (hG : GlobalFnsSt) (hC : CubeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    (f g : P.A ⟶ P.A) [IsMonHom f] [IsMonHom g] (h : RosatiAdj P.A P.L f g) {T : Over S} (k : ℕ)
    (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs P.A P.L k (x ≫ f) y e ↔ WeilIs P.A P.L k x (y ≫ g) e := by
  obtain ⟨r, hr, ⟨c⟩⟩ := PolAV_exists_cubical hC P
  exact weilIs_rosati c hG P.isAb f g h hx hy e

end GlobalTheory
