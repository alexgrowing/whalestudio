import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cubN_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k n : ℕ) (b m x : A) :
    cubN θ (k * n) b m x = cubN θ k b (m ^ n) x * cubN θ n 1 m x ^ k := by
  have L : ∀ (c : A) (n : ℕ), ∏ l ∈ Finset.range n, θ (c * m ^ l) m x =
      θ c (m ^ n) x * ∏ l ∈ Finset.range n, θ (m ^ l) m x := by
    intro c n
    induction n with
    | zero => simp [h.s01 c 1 x, h.face]
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
      have e := h.coc c (m ^ n) m x
      calc θ c (m ^ n) x * (∏ l ∈ Finset.range n, θ (m ^ l) m x) * θ (c * m ^ n) m x
          = (∏ l ∈ Finset.range n, θ (m ^ l) m x) * (θ (c * m ^ n) m x * θ c (m ^ n) x) := by
            first | ac_rfl | simp only [_root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]
        _ = (∏ l ∈ Finset.range n, θ (m ^ l) m x) * (θ c (m ^ n * m) x * θ (m ^ n) m x) := by rw [e]
        _ = θ c (m ^ n * m) x * ((∏ l ∈ Finset.range n, θ (m ^ l) m x) * θ (m ^ n) m x) := by
            first | ac_rfl | simp only [_root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]
  unfold cubN
  try simp only [_root_.one_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, Finset.prod_range_succ]
    have e2 : ∏ l ∈ Finset.range n, θ (b * m ^ (k * n + l)) m x =
        ∏ l ∈ Finset.range n, θ (b * (m ^ n) ^ k * m ^ l) m x := by
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [pow_add, ← pow_mul, _root_.mul_comm n k, _root_.mul_assoc]
    simp only [e2]
    rw [L (b * (m ^ n) ^ k) n, pow_succ]
    first | ac_rfl | simp only [_root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] | simp only [_root_.one_mul, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]

section Two

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem gen_unique₂ (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J) (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ A).left) (z : Z)
    (J) (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF ((snd A A).left ≫ A.hom) _ (by rw [Over.w]; exact Over.w _)
    (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) hu hu' h Z r z J hJ

theorem val_ros {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε))
    {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem val₂_one {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {u : LB.Gen (LB.LinComb L φ ε)}
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {y : (𝟙_ (Over S)).left} {J}
    (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ h₀ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

theorem ros_swap (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A)
    (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (h₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L))
    (u₂ : LB.Gen (LB.LinComb L (rosatiφ A g f) rosatiε)) (h₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x y : T ⟶ A) : val₂ u₂ z J x y = (val₂ u₁ z J y x)⁻¹ := by
  have key := gen_unique₂ hG hA hL (fun U _ k => by
      refine (prod_neg _ _ (prod_ros f g (snd A A) (fst A A) k)).trans (Eq.trans ?_ (prod_ros g f (fst A A) (snd A A) k).symm)
      rw [mul_comm (snd A A ≫ f), mul_comm (snd A A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (pullGen_isGen _ _ _ _ h₂ (lift (fst A A) (snd A A)).left)
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ h₁ (lift (snd A A) (fst A A)).left)) (fun y I hI => by
      rw [val_inv, val_ros _ _ hI, val_ros _ _ hI, lift_fst, lift_snd, val₂_one n₁ hI, val₂_one n₂ hI, inv_one])
    _ (lift x y).left z J hJ
  rwa [val_inv, val_ros _ _ hJ, val_ros _ _ hJ, lift_fst, lift_snd] at key

end Two

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem ros_pow (hG : GlobalFnsSt) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) {T : Over (Sp R)} {z : T.left}
    {J} (hJ : Good D.P.L z J) (a m x : T ⟶ D.P.A) (k : ℕ) :
    val₂ u z J (a * m ^ k) x * cubN (th D z J) k a m (x ≫ g) =
      cubN (th D z J) k (a ≫ f) (m ≫ f) x * val₂ u z J a x * val₂ u z J m x ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have e := (ros_add D.cub hG D.P.isAb f g u hu n hJ (a * m ^ k) m x).1
    have e' : (a * m ^ k) ≫ f = (a ≫ f) * (m ≫ f) ^ k := by rw [MonObj.mul_comp, MonObj.pow_comp]
    rw [e'] at e
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    rw [pow_succ m, ← _root_.mul_assoc a, pow_succ (val₂ u z J m x)]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul ih
    have a₂ := congrArg Additive.ofMul e
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂

set_option maxHeartbeats 800000 in
theorem sq_add (hG : GlobalFnsSt) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g] (N : ℕ) (hfg : g ≫ f = 𝟙 D.P.A ^ (N + 1))
    (u₂ : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A g f) rosatiε)) (hu₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u₂ (zero2 D.P.A)) (LB.oneGen D.P.L))
    (s : LB.Gen (LB.LinComb D.P.L (K := Fin 3) ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, g.left, (1 : D.P.A ⟶ D.P.A).left]
      ![(N + 1 : ℕ), -1, -(N : ℤ)])) (hs : s.IsGen)
    (s₁ : ∀ (y : (𝟙_ (Over (Sp R))).left) J, Good D.P.L y J → val s (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left y J = 1)
    {T : Over (Sp R)} {z : T.left} {J} (hJ : Good D.P.L z J) (x m : T ⟶ D.P.A) :
    val s (x * m).left z J * (val₂ u₂ z J x (m ≫ g) * cubN (th D z J) (N + 1) 1 m x) =
      val s x.left z J * val s m.left z J := by
  let p := fst D.P.A D.P.A
  let q := snd D.P.A D.P.A
  obtain ⟨t, ht, vt⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) q p (N + 1)
  have ps : ∀ (y : D.P.A ⊗ D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U),
      ∏ i : Fin 3, h (y.left ≫ (![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, g.left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
        (![(N + 1 : ℕ), -1, -(N : ℤ)] : Fin 3 → ℤ) i = h y.left ^ ((N + 1 : ℕ) : ℤ) * h (y ≫ g).left ^ (-1 : ℤ) *
        h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left ^ (-(N : ℤ)) := by
    intro y U _ h
    rw [Fin.prod_univ_three]
    show h (y ≫ 𝟙 _).left ^ _ * h (y ≫ g).left ^ _ * h (y ≫ 1).left ^ _ = _
    rw [Category.comp_id, MonObj.comp_one]; rfl
  have ev : ∀ {T : Over (Sp R)} (x m : T ⟶ D.P.A) {z : T.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s (p * q).left) (LB.mulGen D.P.L _ _ _ _
        (LB.pullGen D.P.L _ _ u₂ (lift p (q ≫ g)).left) t)) (lift x m).left z J =
        val s (x * m).left z J * (val₂ u₂ z J x (m ≫ g) * cubN (th D z J) (N + 1) 1 m x) ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s p.left) (LB.pullGen D.P.L _ _ s q.left)) (lift x m).left z J =
        val s x.left z J * val s m.left z J := fun x m z J hJ => by
    constructor
    · rw [val_mul hJ, val_mul hJ, val_pull hJ, val_ros _ _ hJ, vt _ _ z J hJ, ← Over.comp_left, MonObj.comp_mul,
        MonObj.comp_one, lift_snd_assoc, lift_fst, lift_snd]
    · rw [val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd]
  refine (ev x m hJ).1.symm.trans (Eq.trans (gen_unique₂ hG D.P.isAb D.P.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hs _) (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₂ _) ht))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hs _) (pullGen_isGen _ _ _ _ hs _)) (fun y I hI => ?_) _ _ z J hJ)
    (ev x m hJ).2)
  · refine (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := U) _ (ps p h) (ps q h)).trans (Eq.trans ?_
      (prod_sum₂ (K := Fin 3) (K' := Fin 6 ⊕ Fin 8) (U := U) _ (ps (p * q) h) (prod_sum₂ (K := Fin 6) (K' := Fin 8) (U := U) _
        (prod_ros g f p (q ≫ g) h) (Fin.prod_univ_eight _))).symm)
    have e : (q ≫ g) ≫ f = q ^ (N + 1) := by rw [Category.assoc, hfg, MonObj.comp_pow, Category.comp_id]
    rw [e, MonObj.mul_comp]
    simp only [Sum.elim_inr, Matrix.cons_val]
    rw [_root_.one_mul (q ^ (N + 1)), _root_.one_mul p, mul_comm (q ^ (N + 1)) p, mul_comm q p]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    push_cast
    module
  · have C : IsCub (th D (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
    rw [(ev 1 1 hI).1, (ev 1 1 hI).2, _root_.mul_one (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A), MonObj.one_comp, s₁ y I hI,
      val₂_one n₂ hI, C.N_one]
    simp

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem sq_at_c (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (w0 : O) (hw : TraceFormTwistIso D oa w0) (a : O) (N : ℕ)
    (hN : a * star a = ((N + 1 : ℕ) : O))
    (s : LB.Gen (LB.LinComb D.P.L (K := Fin 3) ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (oa.onB.act a).left,
      (1 : D.P.A ⟶ D.P.A).left] ![(N + 1 : ℕ), -1, -(N : ℤ)])) (hs : s.IsGen)
    (s₁ : ∀ (T : Over (Sp R)) (z : T.left) (J), Good D.P.L z J → val s (1 : T ⟶ D.P.A).left z J = 1)
    {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) (mu : D.X) :
    val s (cP D T mu).left z J * val D.rigK κ.left z J ^ N =
      (val (D.psi mu) κ.left z J)⁻¹ ^ (N + 1) * val (D.psi (a • mu)) κ.left z J := by
  obtain ⟨X, hX, vX⟩ := exists_gen D.P.isLB (K' := Fin 2) (φ' := ![𝟙 D.P.A.left, (oa.onB.act a).left])
    (ε' := ![((1 * (N + 1) : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 3) (K' := PUnit) (U := U) _ (Fin.prod_univ_three _)
        (ppow _ _ N (c := h (1 : D.P.A ⟶ D.P.A).left) ((Fintype.prod_unique _).trans (zpow_one _)))).trans ?_
      rw [Fin.prod_univ_two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, Sum.elim_inl, Matrix.cons_val, Over.id_left, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ s (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig
      D.P.A.hom) N)) (mulGen_isGen _ _ _ _ _ _ _ hs (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) _))
  have vX' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → val X r z J = val s r z J *
      val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (r ≫ D.P.A.hom) z J ^ N :=
    fun Z r z J hJ => by rw [vX Z r z J hJ, val_mul hJ, val_pow, val_pull hJ]
  have H := X_value' hG hB oa w0 hw a (N + 1) hN (Nat.succ_pos N) 1 X hX (corr_of_val D.P.isLB fun y I hI => by
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    have e₂ := s₁ (𝟙_ _) y I hI
    rw [e₁] at e₂
    rw [val_pull hI, Category.id_comp, vX' _ _ y I hI, e₂, show eSec D.P.A ≫ D.P.A.hom = 𝟙 _ from Over.w η[D.P.A],
      _root_.one_mul]
    exact ((val_pow _ _ _ _ _).trans (by simp)).symm) mu
  have e := val_corr hJ H κ.left
  rw [val_pull hJ, val_mul hJ, val_pow, val_pow, val_inv, pow_one] at e
  have e₃ : κ.left ≫ ptK (D.c mu) = (cP D T mu).left := congrArg (fun q => q.left) (comp_cP D κ mu)
  rw [e₃, vX' _ _ z J hJ, Over.w, _root_.one_mul] at e
  refine Eq.trans (congrArg₂ (· * ·) rfl (congrArg (· ^ N) ?_)) e
  exact (val_pull hJ _ _ _).trans (congrArg (fun q => val _ q z J) (Over.w κ))

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)} {F : Type} [Field F]
  [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

set_option maxHeartbeats 800000 in
theorem pull_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N k : ℕ) (χ : D.toPre.X)
    (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u₁ (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (s : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 3) ![(𝟙 D.toPre.P.A : D.toPre.P.A ⟶ D.toPre.P.A).left, (oa.onB.act a).left,
      (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![(N + 1 : ℕ), -1, -(N : ℤ)])) (hs : s.IsGen)
    (s₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.toPre.P.L z J → val s (1 : T ⟶ D.toPre.P.A).left z J = 1)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k (N + 1)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N + 1 - 1))) (jFK (R := V) F)))
    {T : Over (Sp V)} (ρ : T ⟶ DegPre.BF D.toPre F) {z : T.left} {J} (hJ : Good D.toPre.P.L z J) :
    val u ρ.left z J = val s (ρ ≫ DegPre.prB D.toPre F).left z J ^ k *
      val₂ u₁ z J (cP D.toPre T χ) (ρ ≫ DegPre.prB D.toPre F) *
      val D.toPre.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := V) F) z J ^ (k * N) := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have ev : ∀ {T : Over (Sp V)} (ρ : T ⟶ DegPre.BF D.toPre F) {z : T.left} {J}, Good D.toPre.P.L z J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
        (GeneratorPullback.powGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ s (DegPre.prB D.toPre F).left) k)
        (LB.pullGen D.toPre.P.L _ _ u₁ (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left))
        (GeneratorPullback.powGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ D.toPre.rigK
          ((fst (TF (R := V) F) D.toPre.P.A).left ≫ jFK (R := V) F)) (k * N))) ρ.left z J =
      val s (ρ ≫ DegPre.prB D.toPre F).left z J ^ k * val₂ u₁ z J (cP D.toPre T χ) (ρ ≫ DegPre.prB D.toPre F) *
        val D.toPre.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := V) F) z J ^ (k * N) := fun ρ z J hJ => by
    rw [val_mul hJ, val_mul hJ, val_pow, val_pow, val_pull hJ, val_pull hJ D.toPre.rigK, val_ros _ _ hJ, comp_cP,
      ← Category.assoc]; rfl
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  refine (gen_unique' D.toPre.P.isLB (fun U _ h => ?_) (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D.toPre F hG) hu
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hs _) _)
      (pullGen_isGen _ _ _ _ hu₁ _)) (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _))
    (fun y I hI => ?_) _ ρ.left z J hJ).trans (ev ρ hJ)
  · have p₁ := prod_fam D.toPre F (𝟙 _) (star a • χ) (k * (N + 1)) h
    have p₂ := prod_fam D.toPre F (aF D F oa a) χ k h
    have cf : cP D.toPre (DegPre.BF D.toPre F) (star a • χ) = cP D.toPre _ χ ≫ oa.onB.act (star a) := by
      rw [cP, oa.c_lin, ← Category.assoc]; rfl
    have af : aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := lift_snd _ _
    simp only [Over.id_left, Category.id_comp] at p₁
    rw [cf] at p₁
    rw [af] at p₂
    have q₁ : ∏ i : Fin 3, h ((DegPre.prB D.toPre F).left ≫ (![(𝟙 D.toPre.P.A : D.toPre.P.A ⟶ D.toPre.P.A).left,
        (oa.onB.act a).left, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] : Fin 3 → _) i) ^ (![(N + 1 : ℕ), -1, -(N : ℤ)] : Fin 3 → ℤ) i =
        h (DegPre.prB D.toPre F).left ^ ((N + 1 : ℕ) : ℤ) * h (DegPre.prB D.toPre F ≫ oa.onB.act a).left ^ (-1 : ℤ) *
          h (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left ^ (-(N : ℤ)) := by
      rw [Fin.prod_univ_three]
      show h (DegPre.prB D.toPre F ≫ 𝟙 _).left ^ _ * h (DegPre.prB D.toPre F ≫ oa.onB.act a).left ^ _ *
        h (DegPre.prB D.toPre F ≫ 1).left ^ _ = _
      rw [Category.comp_id, MonObj.comp_one]; rfl
    have q₂ : ((fst (TF (R := V) F) D.toPre.P.A).left ≫ jFK (R := V) F) ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A =
        (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := by
      refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D.toPre.P.A) ?_)
      exact (Category.assoc _ _ _).trans (Over.w (fst (TF (R := V) F) D.toPre.P.A))
    refine (prod_sum₂ (K := Fin 3 ⊕ Fin 6) (K' := PUnit) (U := U) _ (prod_sum₂ (K := Fin 3) (K' := Fin 6) (U := U) _
      (ppow _ _ k q₁) (prod_ros _ _ (cP D.toPre _ χ) (DegPre.prB D.toPre F) h))
      (ppow _ _ (k * N) (c := h (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left)
        ((Fintype.prod_unique _).trans ((zpow_one _).trans (congrArg h q₂))))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (prod_neg _ _ p₂)).symm)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    push_cast
    module
  · have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y I) := isCub_cubV D.toPre.cub hI
    have a₁ := val_corr hI hc (𝟙 _)
    rw [val_pull hI, Category.id_comp, val_pull hI, val_pow] at a₁
    have e := (ros_add D.toPre.cub hG D.toPre.P.isAb _ _ u₁ hu₁ n₁ (T := TF (R := V) F) hI 1 1 (cP D.toPre _ χ)).2
    rw [_root_.mul_one, MonObj.one_comp (oa.onB.act a), C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    refine a₁.trans (Eq.trans ?_ (ev (DegPre.zF D.toPre F) hI).symm)
    rw [z₁, z₂, s₁ _ y I hI, mul_eq_left.1 e.symm, one_pow, _root_.one_mul, _root_.one_mul]
    rfl

set_option maxHeartbeats 1600000 in
theorem famFE_of_pullAl (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (w0 : O) (hw : TraceFormTwistIso D.toPre oa w0) (a : O) (N : ℕ)
    (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ) (s : Fam D.toPre F k)
    (s' : ∀ β : D.toPre.X, LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F β) (DegPre.famε (k * N))))
    (h₁ : ∀ χ : D.toPre.X, ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) ∧
      GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N)) (s' (star a • χ))
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left (pullφ D F oa a χ) (pullε k N) u)
    (h₂ : ∀ β : D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (s' β).f j = 0) : DegPre.FamFE D.toPre F (k * N) s' := by
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  intro mu α u hu hc
  refine (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have haa : star a * a = ((N + 1 : ℕ) : O) := (mul_comm _ _).trans hN
  have sm : ∀ χ, star a • (χ + k • a • mu) = star a • χ + (k * (N + 1)) • mu := fun χ => by
    rw [smul_add, smul_comm (star a) k, smul_smul (star a), haa, Nat.cast_smul_eq_nsmul, ← mul_nsmul']
  by_cases hα : ∃ χ, α = star a • χ
  swap
  · have z₁ : ∀ j, (s' α).f j = 0 := h₂ α fun χ h => hα ⟨χ, h⟩
    have z₂ : ∀ j, (s' (α + (k * (N + 1)) • mu)).f j = 0 := h₂ _ fun χ h => hα ⟨χ - k • a • mu, by
      have := sm (χ - k • a • mu)
      rw [sub_add_cancel, ← h] at this
      exact (add_right_cancel this)⟩
    exact ((congrArg (gs _ y _) (z₂ _)).trans (gs_zero _ y _ (hJ.mem _ _))).trans ((congrArg (· * _)
      ((congrArg (gs _ y _) (z₁ _)).trans (gs_zero _ y _ (hJ.mem _ _)))).trans (zero_mul _)).symm
  obtain ⟨χ, rfl⟩ := hα
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u₁, hu₁, n₁⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  obtain ⟨u₂, hu₂, n₂⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ (oa.onB.rosati a)
  obtain ⟨q, hq, q₁⟩ := exists_sq hG oa w0 hw a N haa
  let σ : DegPre.BF D.toPre F ⟶ TF (R := V) F := fst _ _
  let x := DegPre.prB D.toPre F
  let κ : DegPre.BF D.toPre F ⟶ TK V := Over.homMk (σ.left ≫ jFK (R := V) F) ((Category.assoc _ _ _).trans (Over.w σ))
  have cf : ∀ (b : O) ψ, cP D.toPre (DegPre.BF D.toPre F) (b • ψ) = cP D.toPre _ ψ ≫ oa.onB.act b := fun b ψ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have C : IsCub (th D.toPre (T := DegPre.BF D.toPre F) y J) := isCub_cubV D.toPre.cub hJ
  have af : aF D F oa a ≫ x = x ≫ oa.onB.act a := lift_snd _ _
  have as : aF D F oa a ≫ σ = σ := lift_fst _ _
  have hm : ∀ ψ, σ ≫ cP D.toPre _ ψ = cP D.toPre _ ψ := comp_cP D.toPre σ

  obtain ⟨v₁, hv₁, c₁, r₁⟩ := h₁ (χ + k • a • mu)
  obtain ⟨v₂, hv₂, c₂, r₂⟩ := h₁ χ
  obtain ⟨⟨v₃, hv₃, c₃⟩, vv₃⟩ := gen_fe (D := D.toPre) (F := F) hG k (a • mu) χ
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ v₁).1 r₁ _ (𝟙 (DegPre.BF D.toPre F) :).left y J hJ
  have e₂ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ v₂).1 r₂ _ (DegPre.trPt D.toPre F (cP D.toPre _ mu)).left y J hJ
  have e₃ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ v₃).1 (s.fe (a • mu) χ v₃ hv₃ c₃) _ (aF D F oa a).left y J hJ
  have e₄ := (gen_fe hG (k * (N + 1)) mu (star a • χ)).2 u hu hc _ (𝟙 _) y J hJ
  rw [pull_val hG oa a N k _ u₁ hu₁ n₁ q hq q₁ v₁ hv₁ c₁ (𝟙 _) hJ, Category.id_comp, Category.id_comp, Over.id_left,
    Category.id_comp, sm] at e₁
  rw [pull_val hG oa a N k _ u₁ hu₁ n₁ q hq q₁ v₂ hv₂ c₂ _ hJ, tr_pr, tr_fst, hm, ← Over.comp_left] at e₂
  rw [vv₃ v₃ hv₃ c₃ _ _ y J hJ, trF_eq, ← Over.comp_left, as, uVal, ← Category.assoc, as, af, hm, val_famMult σ hJ] at e₃
  rw [uVal_id, Category.id_comp, Over.id_left, hm, val_famMult σ hJ] at e₄
  have cm : DegPre.trPt D.toPre F (cP D.toPre _ mu) ≫ aF D F oa a =
      aF D F oa a ≫ DegPre.trPt D.toPre F (cP D.toPre _ (a • mu)) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, tr_fst]; exact (congrArg (_ ≫ ·) as).trans ((tr_fst _ _ _).trans as.symm)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) af).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
      refine Eq.trans ?_ (congrArg (aF D F oa a ≫ ·) (tr_pr D.toPre F _)).symm
      rw [← Category.assoc, tr_pr, MonObj.mul_comp, MonObj.comp_mul, hm, hm, comp_cP, cf]
      exact congrArg₂ (· * ·) af.symm rfl
  rw [cm] at e₂
  rw [Category.id_comp, trF_eq, e₁, e₂, e₃, e₄]
  refine (_root_.mul_assoc _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ((Units.val_mul _ _).symm.trans
    (Eq.trans (congrArg Units.val ?_) (Units.val_mul _ _)))) (_root_.mul_assoc _ _ _).symm)
  have gf : oa.onB.act a ≫ oa.onB.act (star a) = 𝟙 D.toPre.P.A ^ (N + 1) := by
    rw [← oa.onB.map_mul, haa, ← _root_.mul_one ((N + 1 : ℕ) : O), act_nsmul, oa.onB.map_one]
  have mN : cP D.toPre (DegPre.BF D.toPre F) (a • mu) ≫ oa.onB.act (star a) = cP D.toPre _ mu ^ (N + 1) := by
    rw [cf, Category.assoc, gf, MonObj.comp_pow, Category.comp_id]
  have f₁ := ros_pow hG _ _ u₁ hu₁ n₁ hJ (cP D.toPre (DegPre.BF D.toPre F) χ) (cP D.toPre _ (a • mu)) x k
  rw [mN, ← cf] at f₁
  have f₂ := (ros_add D.toPre.cub hG D.toPre.P.isAb _ _ u₁ hu₁ n₁ (T := DegPre.BF D.toPre F) hJ x (cP D.toPre _ mu)
    (cP D.toPre _ χ)).2
  rw [← cf, ← cf] at f₂
  have f₃₀ := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u₁ hu₁ n₁ χ mu) κ.left)
  have f₃₁ : val (LB.pullGen D.toPre.P.L _ _ u₁ (D.toPre.pt2 χ mu)) κ.left y J =
      val₂ u₁ y J (cP D.toPre (DegPre.BF D.toPre F) χ) (cP D.toPre _ mu) := by
    rw [val_pull hJ, val₂, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ mu, ← comp_lift]; rfl
  have f₃ : val (D.toPre.tau mu (star a • χ)) (σ.left ≫ jFK (R := V) F) y J *
      val₂ u₁ y J (cP D.toPre (DegPre.BF D.toPre F) χ) (cP D.toPre _ mu) =
      val (D.toPre.tau (a • mu) χ) (σ.left ≫ jFK (R := V) F) y J :=
    (congrArg₂ (· * ·) (tau_symm σ hJ _ _) f₃₁.symm).trans (f₃₀.trans (tau_symm σ hJ _ _))
  have f₄ : val q (cP D.toPre (DegPre.BF D.toPre F) mu).left y J * val D.toPre.rigK (σ.left ≫ jFK (R := V) F) y J ^ N =
      (val (D.toPre.psi mu) (σ.left ≫ jFK (R := V) F) y J)⁻¹ ^ (N + 1) *
        val (D.toPre.psi (a • mu)) (σ.left ≫ jFK (R := V) F) y J :=
    sq_at_c hG D.tau_bimult oa w0 hw a N hN q hq q₁ κ hJ mu
  have f₅ := sq_add hG _ _ N gf u₂ hu₂ n₂ q hq (fun y J hJ => q₁ _ y J hJ) (T := DegPre.BF D.toPre F) hJ x (cP D.toPre _ mu)
  rw [ros_swap hG D.toPre.P.isAb D.toPre.P.isLB _ _ u₁ hu₁ n₁ u₂ hu₂ n₂ hJ, ← cf] at f₅
  have f₇ := cubN_mul C k (N + 1) (cP D.toPre _ (star a • χ)) (cP D.toPre _ mu) x
  rw [cPoint_add, cPoint_nsmul, val_pow, val_pow, val_pow, val_pow, f₇]
  apply Additive.ofMul.injective
  have E := fun {p q : ((DegPre.BF D.toPre F).left.presheaf.stalk y)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have g₁ := E f₁; have g₂ := E f₂; have g₃ := E f₃; have g₄ := E (congrArg (· ^ k) f₄); have g₅ := E (congrArg (· ^ k) f₅)
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at g₁ g₂ g₃ g₄ g₅ ⊢
  linear_combination (norm := module) g₁ - g₂ - g₃ - g₄ - g₅

end Main

end ReciprocityTheory.ChartRestriction.G.DVR
