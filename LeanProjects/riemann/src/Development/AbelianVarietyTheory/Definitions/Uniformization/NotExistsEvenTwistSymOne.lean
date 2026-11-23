import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]

theorem TQ.comp_i_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) : (t ≫ Q.i) ≫ Q.q = 1 := by
  rw [Category.assoc, Q.isKernel.w, ← Category.assoc]
  simp only [toUnit_unique (t ≫ toUnit _) (toUnit T)]
  rfl

theorem TQ.Desc.cubV_torus {Q : TQ G X} {P : CP G} (D : Q.Desc P) {T : Over S} {z : T.left} {J}
    (hJ : Good D.M.L.L z J) (h : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S) (x : T ⟶ splitTorus S X) (y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV D.M.c (T := Over.mk (T.hom ≫ 𝟙 S)) z J
      (toBase h (x ≫ Q.i)) (toBase h y) (toBase h u)) = 1 := by
  have e : toBase h (x ≫ Q.i) = 1 := by
    ext
    have h1 := congrArg (fun f => f.left) (TQ.comp_i_q Q x)
    simp only [Over.comp_left] at h1
    rw [one_left] at h1 ⊢
    simp [toBase, h1]
  rw [e]
  exact (isCub_cubV D.M.c hJ).face _ _

private theorem comp_one_uniformization {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (x : T ⟶ T') :
    x ≫ (1 : T' ⟶ G) = 1 := by
  show x ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _)]

private theorem one_comp_of_isMonHom' {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) [IsMonHom q]
    {T : Over S} : (1 : T ⟶ G) ≫ q = 1 := by
  show (toUnit _ ≫ η) ≫ q = toUnit _ ≫ η
  rw [Category.assoc, IsMonHom.one_hom]

private theorem prod_mul_inv_four_eq_of_mul_eq {U : Type} [CommGroup U] {C w a b c d e f g : U}
    (hv : e * f * g * w = a * b * c * d * C) :
    w * a⁻¹ * (w * b⁻¹) * (w * c⁻¹) * (w * d⁻¹) = C * (w * e⁻¹) * (w * f⁻¹) * (w * g⁻¹) := by
  have hC : C = (a * b * c * d)⁻¹ * (e * f * g * w) := by rw [hv]; group
  rw [hC]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem oneGen_isGen_uniformization {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  unfold LB.Gen.IsGen
  simp [LB.oneGen]
  intro i j
  unfold LB.LinComb
  simp

private theorem mul_inv_eq_mul_mul_mul_inv {U : Type} [CommGroup U] (w m s : U) : w * m⁻¹ = s * (w * (m * s)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem eq_mul_inv_of_one_eq_mul_inv_mul {U : Type} [CommGroup U] {a b v : U} (h : 1 = a * b⁻¹ * v) : v = b * a⁻¹ := by
  calc v = (a * b⁻¹)⁻¹ * (a * b⁻¹ * v) := by group
    _ = b * a⁻¹ := by rw [← h]; group

theorem TQ.Desc.exists_even {Q : TQ G X} {P : CP G} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hi := Q.i_hom
  have hq := Q.q_hom
  have hw : PGen D.w := (isGen_iff D.w).1 D.map.gen
  have hF : FormEq (K := PEmpty) (K' := Fin 2) PEmpty.elim PEmpty.elim
      ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] ![1, -1] := by
    intro U _ h
    simp [Fin.prod_univ_two]
  obtain ⟨t, ht, htv⟩ := exists_gen D.M.L.isLB hF (LB.oneGen D.M.L.L) (oneGen_isGen_uniformization _)
  have hc : ∀ k, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] : Fin 2 → _) k ≫ Q.q.left =
      𝟙 _ ≫ (![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] : Fin 2 → _) k := by
    intro k
    fin_cases k
    · show Q.i.left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left]
      simpa using congrArg (fun f => f.left) (TQ.comp_i_q Q (𝟙 _))
    · show (1 : splitTorus S X ⟶ G).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, one_comp_of_isMonHom']
  obtain ⟨a, ha, hpm⟩ := CubTransport.exists_pmaps hw D.M.L.isLB P.L.isLB (𝟙 _) hc t ht
  have key : ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J : (T.left ⟶ Q.B.left) → D.M.L.L.ι)
      (J' : (T.left ⟶ G.left) → P.L.L.ι), Good D.M.L.L z J → Good P.L.L z J' →
      val a x.left z J' = gw D.w (1 : T ⟶ G).left z (J ((1 : T ⟶ G).left ≫ Q.q.left)) (J' (1 : T ⟶ G).left) *
        (gw D.w (x ≫ Q.i).left z (J ((x ≫ Q.i).left ≫ Q.q.left)) (J' (x ≫ Q.i).left))⁻¹ := by
    intro T x z J J' hJ hJ'
    have e1 := CubTransport.val_pmaps hc hpm x.left hJ hJ'
    rw [htv _ _ _ _ hJ, val_one, Fin.prod_univ_two] at e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, ← Over.comp_left,
      comp_one_uniformization] at e1
    exact eq_mul_inv_of_one_eq_mul_inv_mul e1
  refine ⟨⟨a, ha, ?_⟩, ?_⟩
  · intro T x y u z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (x ≫ Q.i) (y ≫ Q.i) (u ≫ Q.i)
    rw [TQ.Desc.cubV_torus D hJ _ x (y ≫ Q.i) (u ≫ Q.i), _root_.one_mul] at hv
    simp only [← MonObj.mul_comp] at hv
    have key' := fun v : T ⟶ splitTorus S X => key T v z J J' hJ hJ'
    simp only [key']
    exact prod_mul_inv_four_eq_of_mul_eq hv
  · intro T x z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hs := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.1 (x ≫ Q.i)
    have e3 : (x ≫ Q.i).left ≫ Q.q.left = (1 : T ⟶ Q.B).left := by
      rw [← Over.comp_left, TQ.comp_i_q]
    have hsym : val D.M.sym ((x ≫ Q.i).left ≫ Q.q.left) z J = 1 := by
      rw [e3]; exact CP.val_sym_one _ hJ
    rw [hsym, _root_.one_mul, ← GrpObj.inv_comp] at hs
    rw [key T x⁻¹ z J J' hJ hJ', key T x z J J' hJ hJ', hs]
    exact mul_inv_eq_mul_mul_mul_inv _ _ _

theorem exists_point_neg_one : ∃ t : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ splitTorus (Spec (CommRingCat.of ℚ)) ℤ,
    t⁻¹ = t ∧ chV t 1 ≠ 1 := by
  let e := splitTorusPointsEquiv (Spec (CommRingCat.of ℚ)) ℤ (𝟙_ (Over (Spec (CommRingCat.of ℚ))))
  refine ⟨e.symm (zpowersHom _ (-1)), ?_, ?_⟩
  · apply e.injective
    rw [map_inv, MulEquiv.apply_symm_apply]
    ext
    simp
  · intro h1
    have h2 := congrArg Units.val h1
    simp [chV, e] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom h2
    rw [map_neg, map_one] at h3
    norm_num at h3

private theorem stalk_neg_one_ne_one_of_over_rat {Z : Scheme.{0}} (z : Z) (f : Z ⟶ Spec (CommRingCat.of ℚ)) :
    (-1 : Z.presheaf.stalk z) ≠ 1 := by
  intro h
  let φ : ℚ →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom)
  have h2 : φ 2 = φ 0 := by
    rw [map_ofNat, map_zero]
    linear_combination -h
  exact absurd (φ.injective h2) (by norm_num)

theorem not_exists_even_twistSym_one :
    ¬ ∃ σ : CubTriv ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).c (𝟙 _), σ.Even := by
  rintro ⟨σ, hσ⟩
  let e := splitTorusPointsEquiv (Spec (CommRingCat.of ℚ)) ℤ (𝟙_ (Over (Spec (CommRingCat.of ℚ))))
  let t := e.symm (zpowersHom _ (-1))
  have ht : t⁻¹ = t := by
    apply e.injective
    rw [map_inv, MulEquiv.apply_symm_apply]
    ext
    simp [t]
  have hc : (chV t 1).val = -1 := by simp [chV, t, e]
  obtain ⟨z⟩ : Nonempty (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).left := ⟨IsLocalRing.closedPoint ℚ⟩
  obtain ⟨J, hJ⟩ := exists_good_pt (((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).L.isLB) z
  have h1 := hσ _ t z J hJ
  rw [ht] at h1
  have hb : val ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).sym (t ≫ 𝟙 _).left z J = 1 :=
    mul_right_cancel (h1.symm.trans (_root_.one_mul _).symm)
  have hb2 := val_scaleGen (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1)
    (CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).sym (t ≫ 𝟙 _).left hJ
  erw [val_sym_triv, _root_.mul_one] at hb2
  have hb3 : gm (t ≫ 𝟙 _).left z ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1) = 1 := hb2.symm.trans hb
  rw [Category.comp_id, gm_charUnit] at hb3
  have hv := congrArg Units.val hb3
  rw [gm_val (𝟙 (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).left) z ⊤ (by simp), Units.val_one, hc] at hv
  simp only [map_neg, map_one] at hv
  exact stalk_neg_one_ne_one_of_over_rat z (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).hom hv

theorem isEmpty_desc_twistSym_one : IsEmpty ((TQ.torus (Spec (CommRingCat.of ℚ)) ℤ).Desc
    ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1)) := by
  constructor
  intro D
  exact not_exists_even_twistSym_one (TQ.Desc.exists_even D)

theorem CubWeil.sq_eq_one_of_weilIs_inv (hG : GlobalFnsSt) (hA : IsAbelianScheme G) {L : RigLB G} {c : CubicalStr G L}
    {N : ℕ} {T : Over S} {x y : T ⟶ G} {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : WeilIs G L.L N x y ζ⁻¹) :
    ζ ^ 2 = 1 := by
  have h2 : CubWeil c N x y ζ⁻¹ := (cubWeil_iff_weilIs hG hA h.1 h.2.1 ζ⁻¹).2 h'
  have e : ζ = ζ⁻¹ := h.unique h2
  calc ζ ^ 2 = ζ * ζ := sq ζ
    _ = ζ * ζ⁻¹ := congrArg (ζ * ·) e
    _ = 1 := mul_inv_cancel ζ

theorem TQ.Desc.nonempty_biTriv {Q : TQ G X} {P : CP G} (D : Q.Desc P) : Nonempty (BiTriv P.c Q.i) := by
  have hi := Q.i_hom
  have hq := Q.q_hom
  have hw : PGen D.w := (isGen_iff D.w).1 D.map.gen
  have hOe : (Oε : Fin 4 → ℤ) = ![1, -1, -1, 1] := rfl
  let φ : Fin 4 → ((splitTorus S X ⊗ G).left ⟶ Q.B.left) := ![(snd (splitTorus S X) G ≫ Q.q).left,
    (1 : splitTorus S X ⊗ G ⟶ Q.B).left, (snd (splitTorus S X) G ≫ Q.q).left, (1 : splitTorus S X ⊗ G ⟶ Q.B).left]
  have hF : FormEq (K := PEmpty) (K' := Fin 4) PEmpty.elim PEmpty.elim φ Oε := by
    intro U _ h
    simp [Fin.prod_univ_four, hOe, φ]
  obtain ⟨t, ht, htv⟩ := exists_gen D.M.L.isLB hF (LB.oneGen D.M.L.L) (oneGen_isGen_uniformization _)
  have hc : ∀ k, lamφ Q.i k ≫ Q.q.left = 𝟙 _ ≫ φ k := by
    intro k
    fin_cases k
    · show ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left ≫ Q.q.left =
        𝟙 _ ≫ (snd (splitTorus S X) G ≫ Q.q).left
      rw [Category.id_comp, ← Over.comp_left, MonObj.mul_comp, TQ.comp_i_q, _root_.one_mul]
    · show (fst (splitTorus S X) G ≫ Q.i).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⊗ G ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, TQ.comp_i_q]
    · show (snd (splitTorus S X) G).left ≫ Q.q.left = 𝟙 _ ≫ (snd (splitTorus S X) G ≫ Q.q).left
      rw [Category.id_comp, Over.comp_left]
    · show (1 : splitTorus S X ⊗ G ⟶ G).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⊗ G ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, one_comp_of_isMonHom']
  obtain ⟨a, ha, hpm⟩ := CubTransport.exists_pmaps hw D.M.L.isLB P.L.isLB (𝟙 _) hc t ht
  have key : ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left)
      (J : (T.left ⟶ Q.B.left) → D.M.L.L.ι) (J' : (T.left ⟶ G.left) → P.L.L.ι), Good D.M.L.L z J →
      Good P.L.L z J' → val a (lift t x).left z J' =
        (gw D.w ((t ≫ Q.i) * x).left z (J (((t ≫ Q.i) * x).left ≫ Q.q.left)) (J' ((t ≫ Q.i) * x).left) *
          (gw D.w (t ≫ Q.i).left z (J ((t ≫ Q.i).left ≫ Q.q.left)) (J' (t ≫ Q.i).left))⁻¹ *
          (gw D.w x.left z (J (x.left ≫ Q.q.left)) (J' x.left))⁻¹ *
          gw D.w (1 : T ⟶ G).left z (J ((1 : T ⟶ G).left ≫ Q.q.left)) (J' (1 : T ⟶ G).left))⁻¹ := by
    intro T t x z J J' hJ hJ'
    have e1 := CubTransport.val_pmaps hc hpm (lift t x).left hJ hJ'
    rw [htv _ _ _ _ hJ, val_one] at e1
    simp only [Fin.prod_univ_four] at e1
    have k0 : (lift t x).left ≫ lamφ Q.i 0 = ((t ≫ Q.i) * x).left := by
      show (lift t x).left ≫ ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left = _
      rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have k1 : (lift t x).left ≫ lamφ Q.i 1 = (t ≫ Q.i).left := by
      show (lift t x).left ≫ (fst (splitTorus S X) G ≫ Q.i).left = _
      rw [← Over.comp_left, lift_fst_assoc]
    have k2 : (lift t x).left ≫ lamφ Q.i 2 = x.left := by
      show (lift t x).left ≫ (snd (splitTorus S X) G).left = _
      rw [← Over.comp_left, lift_snd]
    have k3 : (lift t x).left ≫ lamφ Q.i 3 = (1 : T ⟶ G).left := by
      show (lift t x).left ≫ (1 : splitTorus S X ⊗ G ⟶ G).left = _
      rw [← Over.comp_left, comp_one_uniformization]
    have o0 : Oε 0 = 1 := rfl
    have o1 : Oε 1 = -1 := rfl
    have o2 : Oε 2 = -1 := rfl
    have o3 : Oε 3 = 1 := rfl
    rw [k0, k1, k2, k3, o0, o1, o2, o3] at e1
    simp only [zpow_one, zpow_neg_one, Category.comp_id] at e1
    exact eq_inv_of_mul_eq_one_right e1.symm
  refine ⟨⟨a, ha, ?_, ?_⟩⟩
  · intro T t t' x z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (t ≫ Q.i) (t' ≫ Q.i) x
    rw [TQ.Desc.cubV_torus D hJ _ t (t' ≫ Q.i) x, _root_.one_mul] at hv
    rw [key T (t * t') x z J J' hJ hJ', key T t x z J J' hJ hJ', key T t' x z J J' hJ hJ', MonObj.mul_comp]
    rw [eq_inv_mul_of_mul_eq hv.symm]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro T t x x' z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (t ≫ Q.i) x x'
    rw [TQ.Desc.cubV_torus D hJ _ t x x', _root_.one_mul] at hv
    rw [key T t (x * x') z J J' hJ hJ', key T t x z J J' hJ hJ', key T t x' z J J' hJ hJ',
      show (t ≫ Q.i) * (x * x') = (t ≫ Q.i) * x * x' from (_root_.mul_assoc _ _ _).symm]
    rw [eq_inv_mul_of_mul_eq hv.symm]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

private theorem gs_id_appLE_eq_gs {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Y, U))
    (z : Z) : gs (𝟙 Z) z ⊤ ((f.appLE U ⊤ h).hom a) = gs f z U a := by
  rw [gs_eq (𝟙 Z) z ⊤ (by simp), gs_eq f z U (h (by simp))]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_id, RingHom.id_apply, CommRingCat.comp_apply]
  exact Z.presheaf.germ_res_apply (homOfLE h) z _ _

private theorem gs_id_appTop_eq_gs {Y Z : Scheme.{0}} (f : Z ⟶ Y) (a : Γ(Y, ⊤)) (z : Z) :
    gs (𝟙 Z) z ⊤ (f.appTop.hom a) = gs f z ⊤ a := by
  rw [gs_eq (𝟙 Z) z ⊤ (by simp), gs_eq f z ⊤ (by simp)]
  simp [Scheme.Hom.appTop] <;> rfl

set_option maxHeartbeats 1000000 in
private theorem exists_tq_i_eq_of_isAbelianScheme {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : ∃ Q : TQ (thickObj R I e G) D.X, Q.i = g.i := by
  refine ⟨{
      B := thickObj R I e D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := ?_ }, rfl⟩
  intro b χ
  have hq := g.q_hom
  have hi := g.i_hom
  have hφ : ∀ k, D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k =
      ((Over.map (thick R I e)).map g.q).left ≫ D.Oφ (DegPre.prBe I D e) χ k := by
    intro k
    fin_cases k
    · show (lift ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) (toUnit _ ≫ D.c χ) ≫ μ).left =
        ((Over.map (thick R I e)).map g.q).left ≫ (lift (DegPre.prBe I D e) (toUnit _ ≫ D.c χ) ≫ μ).left
      rw [← Over.comp_left, ← Category.assoc, comp_lift, ← Category.assoc _ (toUnit _),
        toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · show (toUnit _ ≫ D.c χ).left = ((Over.map (thick R I e)).map g.q).left ≫ (toUnit _ ≫ D.c χ).left
      rw [← Over.comp_left, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · show ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e).left = _
      rw [Over.comp_left]
      rfl
    · show (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.P.A]).left =
        ((Over.map (thick R I e)).map g.q).left ≫
          (toUnit ((Over.map (thick R I e)).obj (thickObj R I e D.P.A)) ≫ η[D.P.A]).left
      rw [← Over.comp_left, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  choose j hj using fun k => exists_chart D.P.isLB (D.Oφ (DegPre.prBe I D e) χ k b)
  refine ⟨LB.wchart D.P.L (D.Oφ (DegPre.prBe I D e) χ) j, Set.mem_iInter.2 hj, ?_⟩
  have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ (DegPre.prBe I D e) χ) j ≤
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := by
    intro y hy
    refine Set.mem_iInter.2 fun k => ?_
    rw [Set.mem_preimage, hφ k]
    exact Set.mem_iInter.1 hy k
  refine ⟨res hle ((g.t χ).s j), ?_⟩
  intro Z t' g' h₁ h₂
  have ht := g.t_gen χ
  have hw := g.t_weight χ
  have mz : ∀ {W : Scheme.{0}} (w : W), w ∈ (⊤ : W.Opens) := fun _ => by simp
  apply fn_ext
  intro z _
  rw [gs_mul (𝟙 Z.left) z ⊤ (mz _), gs_id_appLE_eq_gs, gs_id_appLE_eq_gs, gs_id_appTop_eq_gs,
    ]
  erw [gs_unit ((t' ≫ g.i) * g').left z _ (h₁ (mz z)), gs_unit g'.left z _ (h₂ (mz z)),
    gs_unit t'.left z ⊤ (mz _), ← Units.val_mul]
  congr 1
  erw [gm_res ((t' ≫ g.i) * g').left z hle (h₁ (mz z)), gm_res g'.left z hle (h₂ (mz z))]
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
  have h1q : (t' ≫ g.i) ≫ g.q = 1 := by
    rw [Category.assoc, g.isKernel.w, ← Category.assoc, toUnit_unique (t' ≫ toUnit _) (toUnit _)]
    rfl
  have e12 : ∀ k, ((t' ≫ g.i) * g').left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k =
      g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k := by
    intro k
    rw [hφ k, ← Category.assoc, ← Category.assoc]
    congr 1
    show ((t' ≫ g.i) * g').left ≫ g.q.left = g'.left ≫ g.q.left
    rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, h1q, _root_.one_mul]
  have hc := val_corr hJ hw (lift t' g').left
  rw [val_pull hJ, val_mul hJ, val_pull hJ] at hc
  have em : (lift t' g').left ≫ (lift (fst (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G) ≫ g.i) (snd (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G)) ≫ μ).left = ((t' ≫ g.i) * g').left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
    rfl
  have es : (lift t' g').left ≫ (snd (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G)).left = g'.left := by
    rw [← Over.comp_left, lift_snd]
  rw [em, es] at hc
  have hcg : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t' g').left z J =
      gm t'.left z ⊤ (charUnit _ D.X χ) := by
    show gm _ z _ (res _ (pullU _ ⊤ (charUnit _ D.X χ))) = _
    erw [gm_res, gm_pull, ← Over.comp_left, lift_fst]
    all_goals simp [LB.wchart]
  rw [hcg] at hc
  have m1 : ((t' ≫ g.i) * g').left z ∈
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := hle (h₁ (mz z))
  have m2 : g'.left z ∈
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := hle (h₂ (mz z))
  erw [gen_trans ht _ z m1 (hJ.mem _ ((t' ≫ g.i) * g').left), gen_trans ht _ z m2 (hJ.mem _ g'.left)]
  have hv := hc
  simp only [val, e12] at hv
  simp only [e12]
  have etr : trF (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) Oinvε ((t' ≫ g.i) * g').left z j
      (fun k => J (g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k)) =
      trF (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) Oinvε g'.left z j
      (fun k => J (g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k)) := by
    simp only [trF, e12]
  rw [etr, hv]
  exact _root_.mul_left_comm _ _ _

theorem nonempty_tq_of_gtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : ∃ Q : TQ (thickObj R I e G) D.X, Q.i = g.i := exists_tq_i_eq_of_isAbelianScheme g hB

end GlobalTheory.UU
end
