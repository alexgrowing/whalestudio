import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

set_option maxHeartbeats 800000 in
theorem exists_sq_val (oa : D.OAct O) (w0 a : O) (N : ℕ) (haa : star a * a = ((N + 1 : ℕ) : O))
    (u₀ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left,
      (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2])) (hu₀ : u₀.IsGen)
    (u₂ : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act a) (oa.onB.act (star a))) rosatiε)) (hu₂ : u₂.IsGen) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := Fin 3) ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (oa.onB.act a).left,
        (1 : D.P.A ⟶ D.P.A).left] ![(N + 1 : ℕ), -1, -(N : ℤ)]), s.IsGen ∧
      ∀ (T : Over (Sp R)) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → val s ρ.left z J =
        val u₀ (ρ ≫ oa.onB.act a).left z J * (val u₀ ρ.left z J ^ (N + 1))⁻¹ *
          ((val₂ u₂ z J ρ (ρ ≫ oa.onB.act a ≫ oa.onB.act w0))⁻¹ *
            (cubN (cubV D.cub z J) (N + 1) 1 (ρ ≫ oa.onB.act w0) ρ)⁻¹) := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := oa.onB.hom w0
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
  refine ⟨s, hs, fun T ρ z J hJ => ?_⟩
  have x₁ : ρ ≫ x = ρ := Category.comp_id _
  have b₂ : val (LB.pullGen D.P.L _ _ u₀ x.left) ρ.left z J = val u₀ ρ.left z J := by
    rw [val_pull hJ, ← Over.comp_left, x₁]
  have b₃ : val (LB.pullGen D.P.L _ _ u₂ (lift x (g ≫ w)).left) ρ.left z J = val₂ u₂ z J ρ (ρ ≫ g ≫ w) := by
    rw [val_pull hJ, ← Over.comp_left, comp_lift, x₁]; rfl
  have b₄ := vt T ρ z J hJ
  rw [x₁, MonObj.comp_one] at b₄
  rw [vs _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv, val_pow, b₂, b₃, b₄, val_pull hJ]
  rfl

section K

variable {y : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J)
include hJ

theorem tauK_symm (a b : D.X) : val (D.tau a b) (𝟙 _) y J = val (D.tau b a) (𝟙 _) y J := by
  have e : ∀ a b : D.X, val (D.tau a b) (𝟙 _) y J = val (D.psi (a + b)) (𝟙 _) y J * (val (D.psi a) (𝟙 _) y J)⁻¹ *
      (val (D.psi b) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [e, e, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ y J)]

theorem tauK_mul (hB : D.TauBimult) (a a' b : D.X) :
    val (D.tau (a + a') b) (𝟙 _) y J * cubV D.cub (T := TK R) y J (cP D _ a) (cP D _ a') (cP D _ b) =
      val (D.tau a b) (𝟙 _) y J * val (D.tau a' b) (𝟙 _) y J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  have e := val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

theorem tauK_nsmul (hB : D.TauBimult) (a b : D.X) (n : ℕ) :
    val (D.tau (n • a) b) (𝟙 _) y J * cubN (cubV D.cub (T := TK R) y J) n 1 (cP D _ a) (cP D _ b) =
      val (D.tau a b) (𝟙 _) y J ^ n := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  induction n with
  | zero =>
    have t := tauK_mul hJ hB 0 0 b
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    rw [zero_nsmul, pow_zero, mul_eq_left.1 t.symm]; exact _root_.one_mul _
  | succ n ih =>
    have e := tauK_mul hJ hB (n • a) a b
    rw [cPoint_nsmul] at e
    rw [succ_nsmul, cubN, Finset.prod_range_succ, _root_.one_mul, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ, ← ih,
      cubN, mul_right_comm]

end K

set_option maxHeartbeats 800000 in
theorem X_value' (hGF : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (w0 : O) (hΨ : TraceFormTwistIso D oa w0)
    (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (X : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (oa.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hX : X.IsGen)
    (hXn : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ X (eSec D.P.A))
        (GeneratorPullback.powGen D.P.L _ _ D.rig (k * (N - 1))))
    (mu : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ X (ptK (D.c mu)))
      (LB.mulGen D.P.L _ _ _ _
        (GeneratorPullback.powGen D.P.L _ _ (LB.invGen D.P.L _ _ (D.psi mu)) (k * N))
        (GeneratorPullback.powGen D.P.L _ _ (D.psi (a • mu)) k)) := by
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := oa.onB.hom w0
  have haa : star a * a = ((N + 1 : ℕ) : O) := (mul_comm _ _).trans hN
  obtain ⟨u₂, hu₂, n₂⟩ := exists_ros hGF D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
  obtain ⟨u₀, hu₀, n₀, hψ⟩ := hΨ
  obtain ⟨s, hs, vs⟩ := exists_sq_val oa w0 a N haa u₀ hu₀ u₂ hu₂
  have vX : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → val X r z J = val s r z J ^ k *
      val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (r ≫ D.P.A.hom) z J ^ (k * N) := by
    intro Z r z J hJ
    have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → val (LB.mulGen D.P.L _ _ _ _
        (GeneratorPullback.powGen D.P.L _ _ s k) (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig
          D.P.A.hom) (k * N))) r z J = val s r z J ^ k * val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A)
          (ε := fun _ => 1) D.rig (r ≫ D.P.A.hom) z J ^ (k * N) := fun Z r z J hJ => by
      rw [val_mul hJ, val_pow, val_pow, val_pull hJ]
    refine (gen_unique' D.P.isLB (fun U _ h => ?_) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hGF _ _ D.P.isAb).2 hX
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hs _) (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) _))
      (fun y I hI => ?_) Z r z J hJ).trans (ev Z r z J hJ)
    · refine (prod_sum₂ (K := Fin 3) (K' := PUnit) (U := U) _ (ppow _ _ k (Fin.prod_univ_three _))
        (ppow _ _ (k * N) (c := h (1 : D.P.A ⟶ D.P.A).left) ((Fintype.prod_unique _).trans (zpow_one _)))).trans ?_
      rw [Fin.prod_univ_two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, Sum.elim_inl, Matrix.cons_val, Over.id_left, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      push_cast
      module
    · have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
      have w₀ : val u₀ (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left y I = 1 :=
        (val_pull hI u₀ (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hI n₀ _).trans (val_one _))
      have r₂ : val₂ u₂ y I (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) 1 = 1 := by
        have e := (ros_add D.cub hGF D.P.isAb _ _ u₂ hu₂ n₂ (T := 𝟙_ _) hI 1 1 1).2
        rw [_root_.mul_one, C.face, MonObj.one_comp, C.face, _root_.mul_one, _root_.one_mul] at e
        exact mul_eq_left.1 e.symm
      have s₁ := vs (𝟙_ _) 1 y I hI
      rw [MonObj.one_comp (oa.onB.act a), MonObj.one_comp (oa.onB.act a ≫ oa.onB.act w0), w₀, r₂, C.N_one, e₁] at s₁
      have a₁ := val_corr hI hXn (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁
      refine a₁.trans (Eq.trans ?_ (ev _ _ y I hI).symm)
      rw [s₁, show eSec D.P.A ≫ D.P.A.hom = 𝟙 _ from Over.w η[D.P.A]]
      exact (val_pow _ _ _ _ _).trans (by simp)
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have cf : ∀ (x : O) χ, cP D (TK R) (x • χ) = cP D (TK R) χ ≫ oa.onB.act x := fun x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have W : ∀ χ, val (D.tau χ (w0 • χ)) (𝟙 _) y J * val u₀ (cP D (TK R) χ).left y J =
      val (D.psi χ) (𝟙 _) y J * val D.rigK (𝟙 _) y J := fun χ => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hψ χ) (𝟙 _)).trans (val_mul hJ _ _ _))
    rwa [val_pull hJ, Category.id_comp] at e
  have B := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal a u₂ hu₂ n₂ mu (w0 • a • mu)) (𝟙 _))
  rw [val_pull hJ, Category.id_comp] at B
  have sm : star a • w0 • a • mu = (N + 1) • w0 • mu := by
    rw [smul_smul, smul_smul, mul_right_comm, haa, mul_smul, Nat.cast_smul_eq_nsmul]
  have B₀ : val (D.tau (a • mu) (w0 • a • mu)) (𝟙 _) y J * val₂ u₂ y J (cP D (TK R) mu) (cP D (TK R) (w0 • a • mu)) =
      val (D.tau mu (star a • w0 • a • mu)) (𝟙 _) y J := B
  have B' := B₀.trans ((congrArg (fun q => val (D.tau mu q) (𝟙 _) y J) sm).trans (tauK_symm hJ _ _))
  have T := tauK_nsmul hJ hB (w0 • mu) mu (N + 1)
  rw [tauK_symm hJ (w0 • mu) mu] at T
  have S := vs _ (cP D (TK R) mu) y J hJ
  rw [← Category.assoc, ← cf, ← cf, ← cf] at S
  have Rg : val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      ((cP D (TK R) mu).left ≫ D.P.A.hom) y J = val D.rigK (𝟙 _) y J := by
    rw [Over.w]; exact ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)).symm
  rw [val_pull hJ, Category.id_comp, val_mul hJ, val_pow, val_pow, val_inv]
  refine (vX _ (cP D (TK R) mu).left y J hJ).trans ?_
  have S' : val s (cP D (TK R) mu).left y J * val D.rigK (𝟙 _) y J ^ N =
      (val (D.psi mu) (𝟙 _) y J)⁻¹ ^ (N + 1) * val (D.psi (a • mu)) (𝟙 _) y J := by
    rw [S]
    apply Additive.ofMul.injective
    have E := fun {p q : ((TK R).left.presheaf.stalk y)ˣ} (e : p = q) => congrArg Additive.ofMul e
    have w₁ := E (W (a • mu)); have w₂ := E (congrArg (· ^ (N + 1)) (W mu)); have b := E B'; have t := E T
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at w₁ w₂ b t ⊢
    linear_combination (norm := module) w₁ - w₂ - b - t
  rw [Rg, mul_comm k N, pow_mul, ← mul_pow, S', mul_pow, ← pow_mul, mul_comm (N + 1) k]

section Closed

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (IsLocalRing.maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem X_value (hGF : GlobalFnsSt) (oa : D.toPre.OAct O) (w0 : O) (hΨ : Geo.Tor.TraceFormTwistIso D.toPre oa w0)
    (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hX : X.IsGen)
    (hXn : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
        (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))))
    (mu : D.toPre.X) :
    LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (ptK (D.toPre.c mu)))
      (LB.mulGen D.toPre.P.L _ _ _ _
        (GeneratorPullback.powGen D.toPre.P.L _ _ (LB.invGen D.toPre.P.L _ _ (D.toPre.psi mu)) (k * N))
        (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (a • mu)) k)) := by
  exact X_value' hGF D.tau_bimult oa w0 hΨ a N hN hN1 k X hX hXn mu

end Closed

end ReciprocityTheory.ChartRestriction.G.DVR
