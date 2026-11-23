import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

structure IsCub (θ : A → A → A → U) : Prop where
  face : ∀ x y, θ 1 x y = 1
  s01 : ∀ x y z, θ x y z = θ y x z
  s12 : ∀ x y z, θ x y z = θ x z y
  coc : ∀ x x' x'' y, θ (x * x') x'' y * θ x x' y = θ x (x' * x'') y * θ x' x'' y

def cubN (θ : A → A → A → U) (k : ℕ) (a m x : A) : U := ∏ i ∈ Finset.range k, θ (a * m ^ i) m x

namespace IsCub

variable {θ : A → A → A → U} (h : IsCub θ)
include h

theorem face₃ (x y : A) : θ x y 1 = 1 := by
  rw [h.s12 x y 1, h.s01 x 1 y, h.face]

theorem face₂ (x y : A) : θ x 1 y = 1 := by
  rw [h.s01 x 1 y, h.face]

theorem compat (x x' y y' : A) :
    θ (x * x') y y' * θ x x' y' * θ x x' y = θ x x' (y * y') * θ x y y' * θ x' y y' := by
  have c1 := h.coc x x' y y'
  have c2 := h.coc x' y y' x
  have e1 : θ x (x' * y) y' = θ (x' * y) y' x := by rw [h.s01 x (x' * y) y', h.s12 (x' * y) x y']
  have e2 : θ x' y x = θ x x' y := by rw [h.s12 x' y x, h.s01 x' x y]
  have e3 : θ x' (y * y') x = θ x x' (y * y') := by rw [h.s12 x' (y * y') x, h.s01 x' x (y * y')]
  have e4 : θ y y' x = θ x y y' := by rw [h.s12 y y' x, h.s01 y x y']
  rw [e2, e3, e4] at c2
  rw [e1] at c1
  calc θ (x * x') y y' * θ x x' y' * θ x x' y = θ (x' * y) y' x * θ x' y y' * θ x x' y := by rw [c1]
    _ = θ (x' * y) y' x * θ x x' y * θ x' y y' := by ac_rfl
    _ = θ x x' (y * y') * θ x y y' * θ x' y y' := by rw [c2]

theorem N_one (k : ℕ) (a m : A) : cubN θ k a m 1 = 1 := Finset.prod_eq_one fun _ _ => h.face₃ _ _

theorem N_split (k : ℕ) (a m x : A) : cubN θ k a m x = θ a (m ^ k) x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face₂]
  | succ k ih =>
    have hc := h.coc a (m ^ k) m x
    unfold cubN at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, _root_.one_mul, _root_.pow_succ]
    set P := ∏ i ∈ Finset.range k, θ (1 * m ^ i) m x
    calc θ a (m ^ k) x * P * θ (a * m ^ k) m x = P * (θ (a * m ^ k) m x * θ a (m ^ k) x) := by ac_rfl
      _ = P * (θ a (m ^ k * m) x * θ (m ^ k) m x) := by rw [hc]
      _ = θ a (m ^ k * m) x * (P * θ (m ^ k) m x) := by ac_rfl

theorem N_add (k : ℕ) (a m x b : A) :
    cubN θ k a m (x * b) * θ a x b * θ m x b ^ k = θ (a * m ^ k) x b * cubN θ k a m x * cubN θ k a m b := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have hc := h.compat (a * m ^ k) m x b
    unfold cubN at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, _root_.pow_succ,
      _root_.pow_succ, ← _root_.mul_assoc a]
    set Cxb := ∏ i ∈ Finset.range k, θ (a * m ^ i) m (x * b)
    set Cx := ∏ i ∈ Finset.range k, θ (a * m ^ i) m x
    set Cb := ∏ i ∈ Finset.range k, θ (a * m ^ i) m b
    calc Cxb * θ (a * m ^ k) m (x * b) * θ a x b * (θ m x b ^ k * θ m x b)
        = (Cxb * θ a x b * θ m x b ^ k) * (θ (a * m ^ k) m (x * b) * θ m x b) := by ac_rfl
      _ = (θ (a * m ^ k) x b * Cx * Cb) * (θ (a * m ^ k) m (x * b) * θ m x b) := by rw [ih]
      _ = Cx * Cb * (θ (a * m ^ k) m (x * b) * θ (a * m ^ k) x b * θ m x b) := by ac_rfl
      _ = Cx * Cb * (θ (a * m ^ k * m) x b * θ (a * m ^ k) m b * θ (a * m ^ k) m x) := by rw [← hc]
      _ = θ (a * m ^ k * m) x b * (Cx * θ (a * m ^ k) m x) * (Cb * θ (a * m ^ k) m b) := by ac_rfl

theorem comm (k : ℕ) (a m b x : A) (Sa Sm Sam τa τy τay : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : τay * θ a (b ^ k) m = τa * τy) (h₃ : τy * cubN θ k 1 b m = Sm ^ k) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Sam) =
      cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) := by
  have rot : ∀ p q r, θ p q r = θ q r p := fun p q r => by rw [h.s01 p q r, h.s12 q p r]
  have hmx : θ m x b = θ b x m := by rw [h.s01 m x b, h.s12 x m b, h.s01 x b m]
  have eSam : Sam = Sa * Sm ^ k * (cubN θ k a m b)⁻¹ := eq_mul_inv_of_mul_eq h₁
  have eτay : τay = τa * τy * (θ a (b ^ k) m)⁻¹ := eq_mul_inv_of_mul_eq h₂
  have eSm : Sm ^ k = τy * cubN θ k 1 b m := h₃.symm
  have e1 : cubN θ k a m (x * b) =
      θ (a * m ^ k) x b * cubN θ k a m x * cubN θ k a m b * (θ a x b * θ m x b ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← _root_.mul_assoc]; exact h.N_add k a m x b
  have e2 : cubN θ k a b (x * m) =
      θ (a * b ^ k) x m * cubN θ k a b x * cubN θ k a b m * (θ a x m * θ b x m ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← _root_.mul_assoc]; exact h.N_add k a b x m
  have c1 := h.coc a (m ^ k) (b ^ k) x
  have c2 := h.coc a (b ^ k) (m ^ k) x
  rw [_root_.mul_comm (b ^ k) (m ^ k), ← h.s01 (m ^ k) (b ^ k) x] at c2
  have c3 := h.coc x b m a
  have c4 := h.coc x m b a
  rw [_root_.mul_comm m b, h.s01 m b a] at c4
  have c1' := eq_mul_inv_of_mul_eq c1
  have c2' := eq_mul_inv_of_mul_eq c2
  have c3' := eq_mul_inv_of_mul_eq c3
  have c4' := eq_mul_inv_of_mul_eq c4
  rw [eSam, eτay, eSm, e1, e2, h.N_split k (a * m ^ k) b x, h.N_split k (a * b ^ k) m x, h.N_split k a m x,
    h.N_split k a b x, h.N_split k a b m, c1', c2', rot a (x * b) m, rot a (x * m) b, c3', c4', rot a x b,
    rot a x m, hmx]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end IsCub

end Alg

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

def cubV {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (lift x (lift x' y)).left z J

theorem val_cub {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J : (T'.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J)
    (x x' y : T ⟶ G) : val (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left) ρ.left z J =
      cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]; rfl

theorem isCub_cubV {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J) : IsCub (cubV c z J) where
  face x y := by
    have := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at this
    refine Eq.trans ?_ this
    refine Eq.trans ?_ (val_cub c (lift x y) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  s01 x y w := by
    have := (val_corr hJ c.cubeSymmetric_swap_first (lift x (lift y w)).left).trans (val_cub c (lift x (lift y w)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  s12 x y w := by
    have := (val_corr hJ c.cubeSymmetric_swap_last (lift x (lift y w)).left).trans (val_cub c (lift x (lift y w)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  coc x x' x'' y := by
    have := val_corr hJ c.cocycle (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) (val_cub c _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) (val_cub c _ hJ _ _ _))))
    have a₀ : lift x (lift x' (lift x'' y)) ≫ x4 G 0 = x := by simp [x4]
    have a₁ : lift x (lift x' (lift x'' y)) ≫ x4 G 1 = x' := by simp [x4]
    have a₂ : lift x (lift x' (lift x'' y)) ≫ x4 G 2 = x'' := by simp [x4]
    have a₃ : lift x (lift x' (lift x'' y)) ≫ x4 G 3 = y := by simp [x4]
    have b₀ : lift x (lift x' (lift x'' y)) ≫ padd G (x4 G 0) (x4 G 1) = x * x' :=
      (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
    have b₁ : lift x (lift x' (lift x'' y)) ≫ padd G (x4 G 1) (x4 G 2) = x' * x'' :=
      (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e

theorem prod_cub {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I =
      h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹ := by
  have e : ∀ I : thK, (lift x (lift x' y)).left ≫ thφ G (x3 G) I = (psum G ![x, x', y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x (lift x' y))) (x3 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])))
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I => h (psum G ![x, x', y] I).left ^ ((-1 : ℤ) ^ (3 - I.card)))
    (fun I => congrArg (fun q => h q ^ thε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_cubN {T : Over S} (a m x : T ⟶ G) (k : ℕ) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 8) ![(a * m ^ k * x).left, (a * m ^ k).left, (a * x).left, a.left,
        (m * x).left, m.left, x.left, (1 : T ⟶ G).left] ![1, -1, -1, 1, -k, k, k, -k]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
        val t ρ.left z J = cubN (cubV c z J) k (ρ ≫ a) (ρ ≫ m) (ρ ≫ x) := by
  induction k with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen L.isLB (φ' := ![(a * m ^ 0 * x).left, (a * m ^ 0).left, (a * x).left, a.left,
        (m * x).left, m.left, x.left, (1 : T ⟶ G).left]) (ε' := ![1, -1, -1, 1, -(0 : ℕ), (0 : ℕ), (0 : ℕ), -(0 : ℕ)])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen L.L (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  | succ k ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen L.isLB (φ' := ![(a * m ^ (k + 1) * x).left, (a * m ^ (k + 1)).left, (a * x).left,
        a.left, (m * x).left, m.left, x.left, (1 : T ⟶ G).left])
      (ε' := ![1, -1, -1, 1, -(k + 1 : ℕ), (k + 1 : ℕ), (k + 1 : ℕ), -(k + 1 : ℕ)]) (fun U _ h => by
        refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (a * m ^ k) m x h))).trans ?_
        rw [pow_succ m, ← _root_.mul_assoc a]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
        module)
      (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a * m ^ k) (lift m x)).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      (val_cub c ρ hJ _ _ _)))).trans ?_
    rw [cubN, cubN, Finset.prod_range_succ]
    congr 2
    exact (map_mul (preHom ρ) _ _).trans (congrArg _ (map_pow (preHom ρ) _ _))

theorem gen_unique {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
