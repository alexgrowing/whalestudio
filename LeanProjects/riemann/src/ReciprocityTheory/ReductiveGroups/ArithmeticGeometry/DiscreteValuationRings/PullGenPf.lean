import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem val_pow {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := by
  unfold val
  exact map_pow _ _ _

theorem act_nsmul (oa : D.OAct O) (w : O) (n : ℕ) : oa.onB.act ((n : O) * w) = oa.onB.act w ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, pow_zero]
    have h := oa.onB.map_add 0 0
    rw [add_zero] at h
    have h2 : oa.onB.act 0 * oa.onB.act 0 = oa.onB.act 0 * 1 := by
      rw [_root_.mul_one]; exact h.symm
    exact _root_.mul_left_cancel h2
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, _root_.one_mul, oa.onB.map_add, ih, pow_succ]
    rfl

theorem ppow {K U : Type} [Fintype K] [CommGroup U] (q : K → U) (e : K → ℤ) (n : ℕ) {c : U} (h : ∏ i, q i ^ e i = c) :
    ∏ i, q i ^ ((n : ℤ) * e i) = c ^ n := by
  subst h
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_mul', zpow_natCast]

theorem ros_right_one (hG : GlobalFnsSt) {f g : D.P.A ⟶ D.P.A} [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) {T : Over (Sp R)} {z : T.left}
    {J} (hJ : Good D.P.L z J) (p q : D.P.A ⟶ D.P.A) (hq : (1 : T ⟶ D.P.A) ≫ q = 1) :
    val (LB.pullGen D.P.L _ _ u (lift p q).left) (1 : T ⟶ D.P.A).left z J = 1 := by
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu n hJ 1 1 (1 ≫ p)).2
  rw [_root_.mul_one, MonObj.one_comp g, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  rw [val_pull hJ, ← Over.comp_left, comp_lift, hq]
  exact mul_eq_left.1 e.symm

set_option maxHeartbeats 800000 in

theorem exists_sq (hG : GlobalFnsSt) (oa : D.OAct O) (w0 : O) (hw : TraceFormTwistIso D oa w0) (a : O) (N : ℕ)
    (haa : star a * a = ((N + 1 : ℕ) : O)) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := Fin 3) ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (oa.onB.act a).left,
        (1 : D.P.A ⟶ D.P.A).left] ![(N + 1 : ℕ), -1, -(N : ℤ)]), s.IsGen ∧
      ∀ (T : Over (Sp R)) (z : T.left) (J), Good D.P.L z J → val s (1 : T ⟶ D.P.A).left z J = 1 := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := oa.onB.hom w0
  obtain ⟨u₂, hu₂, n₂⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
  obtain ⟨u₀, hu₀, n₀, -⟩ := hw
  let g := oa.onB.act a
  let f := oa.onB.act (star a)
  let w := oa.onB.act w0
  let x : D.P.A ⟶ D.P.A := 𝟙 _
  obtain ⟨t, ht, vt⟩ := exists_cubN D.cub (1 : D.P.A ⟶ D.P.A) w x (N + 1)
  have hz : (g ≫ w) ≫ f = w ^ (N + 1) := by
    rw [← oa.onB.map_mul, ← oa.onB.map_mul, ← act_nsmul, ← haa]; congr 1; ring
  have pW : ∀ (y : D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U),
      ∏ i : Fin 4, h (y.left ≫ (![(padd D.P.A (𝟙 _) w).left, 𝟙 D.P.A.left, w.left, (toUnit D.P.A ≫ η[D.P.A]).left] :
        Fin 4 → _) i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      h (y * (y ≫ w)).left * h y.left ^ (-2 : ℤ) * (h (y ≫ w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ (2 : ℤ) := by
    intro y U _ h
    have e₀ : y ≫ padd D.P.A (𝟙 _) w = y * (y ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
    have e₃ : y ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) y
    rw [Fin.prod_univ_four]
    show h (y ≫ padd D.P.A (𝟙 _) w).left ^ (1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (-2 : ℤ) * h (y ≫ w).left ^ (-1 : ℤ) *
      h (y ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
    rw [e₀, e₃, Category.comp_id, zpow_one, zpow_neg_one]
  obtain ⟨s, hs, vs⟩ := exists_gen D.P.isLB (K' := Fin 3) (φ' := ![x.left, g.left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![(N + 1 : ℕ), -1, -(N : ℤ)]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 6 ⊕ Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (pW g h) (prod_neg _ _ (ppow _ _ (N + 1) (pW x h))))
        (prod_sum₂ (K := Fin 6) (K' := Fin 8) (U := U) _ (prod_neg _ _ (prod_ros g f x (g ≫ w) h))
          (prod_neg _ _ (Fin.prod_univ_eight _)))).trans ?_
      have a₁ : x ≫ w = w := Category.id_comp _
      have a₂ : x ≫ g = g := Category.id_comp _
      rw [hz, a₁, a₂, Fin.prod_univ_three]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
      rw [_root_.one_mul (w ^ (N + 1)), _root_.one_mul x, mul_comm (w ^ (N + 1)) x, mul_comm w x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u₀ g.left)
      (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ u₀ x.left) (N + 1))))
      (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u₂ (lift x (g ≫ w)).left)) (LB.invGen D.P.L _ _ t)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₀ _) (invGen_isGen _ _ _ _
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu₀ _) _))) (mulGen_isGen _ _ _ _ _ _ _
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu₂ _)) (invGen_isGen _ _ _ _ ht)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have w₀ : val u₀ (1 : T ⟶ D.P.A).left z J = 1 :=
    (val_pull hJ u₀ (eSec D.P.A) T.hom).symm.trans ((val_corr hJ n₀ _).trans (val_one _))
  have g₁ : (1 : T ⟶ D.P.A).left ≫ g.left = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q => q.left) (MonObj.one_comp (X := T) g)
  have x₁ : (1 : T ⟶ D.P.A) ≫ x = 1 := Category.comp_id _
  have b₁ : val (LB.pullGen D.P.L _ _ u₀ g.left) (1 : T ⟶ D.P.A).left z J = 1 := by rw [val_pull hJ, g₁, w₀]
  have b₂ : val (LB.pullGen D.P.L _ _ u₀ x.left) (1 : T ⟶ D.P.A).left z J = 1 := by
    rw [val_pull hJ, ← Over.comp_left, x₁, w₀]
  have b₃ := ros_right_one hG u₂ hu₂ n₂ hJ x (g ≫ w) (MonObj.one_comp (g ≫ w))
  have b₄ : val t (1 : T ⟶ D.P.A).left z J = 1 := by rw [vt T 1 z J hJ, x₁, C.N_one]
  rw [vs _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv, val_pow, b₁, b₂, b₃, b₄]
  simp

set_option maxHeartbeats 800000 in

theorem exists_pullGenB (hG : GlobalFnsSt) (oa : D.OAct O) (w0 : O) (hw : TraceFormTwistIso D oa w0) (a : O) (N : ℕ) (hN : 1 ≤ N)
    (haa : star a * a = (N : O)) (k : ℕ) (χ : D.X) :
    ∃ e : LB.Gen (LB.LinComb D.P.L (K := Fin 8) ![D.famφB (star a • χ) 0, D.famφB (star a • χ) 1, D.famφB (star a • χ) 2,
        D.famφB (star a • χ) 3, (oa.onB.act a).left ≫ D.famφB χ 0, (oa.onB.act a).left ≫ D.famφB χ 1,
        (oa.onB.act a).left ≫ D.famφB χ 2, (oa.onB.act a).left ≫ D.famφB χ 3]
        ![((k * N : ℕ) : ℤ) - 1, 1, -1, 1, -((k : ℤ) - 1), -1, 1, -1]), e.IsGen ∧
      ∀ (T : Over (Sp R)) (z : T.left) (J), Good D.P.L z J →
        val e (1 : T ⟶ D.P.A).left z J = val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          T.hom z J ^ (k * (N - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u₁, hu₁, n₁⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  obtain ⟨s, hs, s₁⟩ := exists_sq hG oa w0 hw a N haa
  let g := oa.onB.act a
  let f := oa.onB.act (star a)
  let x : D.P.A ⟶ D.P.A := 𝟙 _
  have cf : cP D D.P.A (star a • χ) = cP D D.P.A χ ≫ f := by rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨e, he, ve⟩ := exists_gen D.P.isLB (K' := Fin 8) (φ' := ![D.famφB (star a • χ) 0, D.famφB (star a • χ) 1,
      D.famφB (star a • χ) 2, D.famφB (star a • χ) 3, g.left ≫ D.famφB χ 0, g.left ≫ D.famφB χ 1, g.left ≫ D.famφB χ 2,
      g.left ≫ D.famφB χ 3]) (ε' := ![((k * (N + 1) : ℕ) : ℤ) - 1, 1, -1, 1, -((k : ℤ) - 1), -1, 1, -1]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 3 ⊕ Fin 6) (K' := PUnit) (U := U) _
        (prod_sum₂ (K := Fin 3) (K' := Fin 6) (U := U) _ (ppow _ _ k rfl) (prod_ros f g (cP D _ χ) x h))
        (ppow _ _ (k * N) (c := h (1 : D.P.A ⟶ D.P.A).left) ((Fintype.prod_unique _).trans (zpow_one _)))).trans ?_
      have a₁ : D.famφB (star a • χ) 1 = ((cP D D.P.A χ ≫ f) * x).left := congrArg (fun q => q.left)
        ((mul_comm x (cP D D.P.A (star a • χ))).trans (by rw [cf]))
      have a₂ : D.famφB (star a • χ) 2 = (cP D D.P.A χ ≫ f).left := congrArg (fun q => q.left) cf
      have a₃ : g.left ≫ D.famφB χ 1 = (cP D D.P.A χ * (x ≫ g)).left := congrArg (fun q => q.left)
        ((MonObj.comp_mul g x (cP D D.P.A χ)).trans (by rw [comp_cP, mul_comm, Category.comp_id, Category.id_comp]))
      have a₄ : g.left ≫ D.famφB χ 2 = (cP D D.P.A χ).left := congrArg (fun q => q.left) (comp_cP D g χ)
      have a₅ : g.left ≫ D.famφB χ 3 = (1 : D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) g)
      have a₆ : g.left ≫ D.famφB χ 0 = g.left := Category.comp_id _
      have a₇ : D.famφB (star a • χ) 0 = x.left := rfl
      have a₈ : D.famφB (star a • χ) 3 = (1 : D.P.A ⟶ D.P.A).left := rfl
      have a₉ : x ≫ g = g := Category.id_comp _
      rw [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, Fin.prod_univ_eight, Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ s k)
      (LB.pullGen D.P.L _ _ u₁ (lift (cP D _ χ) x).left))
      (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom) (k * N)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hs _) (pullGen_isGen _ _ _ _ hu₁ _))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) _))
  refine ⟨e, he, fun T z J hJ => ?_⟩
  have b₁ := ros_right_one hG u₁ hu₁ n₁ hJ (cP D _ χ) x (Category.comp_id _)
  rw [ve _ _ z J hJ, val_mul hJ, val_mul hJ, val_pow, val_pow, s₁ T z J hJ, b₁, val_pull hJ, Over.w (1 : T ⟶ D.P.A), one_pow,
    _root_.one_mul, _root_.one_mul]
  rfl

theorem pullGen_one (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O) (hw : TraceFormTwistIso D.toPre oa w0)
    (a : O) (N : ℕ) (hN : 1 ≤ N) (haa : star a * a = (N : O)) (k : ℕ) (χ : D.toPre.X)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))) :
    ∃ (m : ℕ) (ψ : Fin m → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (δ : Fin m → ℤ)
      (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)), eB.IsGen ∧
      FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) ψ)
        (Sum.elim (DegPre.famε k) δ) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        val u r z J = val eB (r ≫ (DegPre.prB D.toPre F).left) z J := by
  obtain ⟨e, he, ve⟩ := exists_pullGenB hG oa w0 hw a N hN haa k χ
  refine ⟨8, _, _, e, he, fun U _ h => ?_, fun Z r y J hJ => ?_⟩
  · rw [Fintype.prod_sum_type, Fin.prod_univ_eight, Fin.prod_univ_four, Fin.prod_univ_four]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, Sum.elim_inl, Sum.elim_inr, DegPre.famε, Matrix.cons_val]
    module
  · have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
    have fb : ∀ α i, (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i = DegPre.famφ D.toPre F α i := fun α i => by
      fin_cases i
      · exact Category.comp_id _
      · exact congrArg (fun q => q.left) ((MonObj.comp_mul (DegPre.prB D.toPre F) (𝟙 _) (cP D.toPre _ α)).trans
          (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
      · exact congrArg (fun q => q.left) (comp_cP D.toPre (DegPre.prB D.toPre F) α)
      · exact congrArg (fun q : DegPre.BF D.toPre F ⟶ D.toPre.P.A => q.left)
          (MonObj.comp_one (M := D.toPre.P.A) (DegPre.prB D.toPre F))
    have fa : ∀ i, (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left ≫ D.toPre.famφB χ i =
        (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
      have : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
        congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
      rw [← fb, ← Category.assoc, ← this, Category.assoc]
    have key := gen_unique' D.toPre.P.isLB (fun U _ h => by
        rw [pullφ, pullε, Fintype.prod_sum_type, Fin.prod_univ_eight, Fin.prod_univ_four, Fin.prod_univ_four]
        simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, fb, fa, DegPre.famε, neg_neg, _root_.mul_assoc])
      (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left (congrArg (fun q => q.left) z₁)
      (surj_appTop D.toPre F hG) hu (pullGen_isGen _ _ _ _ he (DegPre.prB D.toPre F).left) (fun y I hI => by
        have a := val_corr hI hc (𝟙 _)
        rw [val_pull hI, Category.id_comp] at a
        rw [a, val_pull hI, val_pull hI, ← Over.comp_left, z₂, ve _ y I hI, Category.id_comp]
        exact (val_pow _ _ _ _ _).trans (congrArg (· ^ (k * (N - 1))) (val_pull hI _ _ _))) _ r y J hJ
    rw [key, val_pull hJ]

theorem pullback_generator_of_psi_weight (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))
    {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O) (hw : TraceFormTwistIso D.toPre oa w0)
    (a : O) (N : ℕ) (hN : 1 ≤ N) (haa : star a * a = (N : O)) (k : ℕ) (χ : D.toPre.X)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))) :
    ∃ (m : ℕ) (ψ : Fin m → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (δ : Fin m → ℤ)
      (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)), eB.IsGen ∧
      FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) ψ)
        (Sum.elim (DegPre.famε k) δ) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) ∧
      ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ ∀ (y : (DegPre.BF D.toPre F).left)
        (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L y J →
        (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val := by
  obtain ⟨m, ψ, δ, eB, hgen, hform, hval⟩ := pullGen_one hG D F oa w0 hw a N hN haa k χ u hu hc
  refine ⟨m, ψ, δ, eB, hgen, hform, 1, ?_, fun y J hJ => ?_⟩
  · simp
  · have h1 := hval _ (𝟙 _) y J hJ
    rw [Category.id_comp] at h1
    have hg : gs (𝟙 _) y ⊤ (gF D.toPre F (1 : F)) = 1 := by
      unfold gs
      rw [dif_pos (by simp)]
      simp only [map_one]
    rw [h1, hg, _root_.one_mul]

theorem pullGen_of (hG : GlobalFnsSt) : PullGenStatement := by
  intro V _ _ _ ϖ hϖ D F _ _ v hv O _ _ _ oa w0 hw a N hN _ haa k _ χ u hu hc
  exact pullback_generator_of_psi_weight hG D F v oa w0 hw a N hN haa k χ u hu hc

end ReciprocityTheory.ChartRestriction.G.DVR
