import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.CubeConst

section General

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem cubV_through (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L')
    (w : LB.Iso L'.L (L.L.pull F)) (hw : w.IsGen) {T : Over S'} (z : T.left) {J J'} (hJ : Good L.L z J)
    (hJ' : Good L'.L z J') (x y u : T ⟶ G') :
    cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * cubV c' z J' x y u := by
  let Y : Over S' := G' ⊗ G' ⊗ G'
  let H : Over.mk (Y.hom ≫ f) ⟶ G ⊗ G ⊗ G :=
    lift (pushHom gp Y (x3 G' 0)) (lift (pushHom gp Y (x3 G' 1)) (pushHom gp Y (x3 G' 2)))
  have hψ : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ F = H.left ≫ thφ G (x3 G) I := fun I => by
    have e₁ := psum_hom (pushHom gp Y) (x3 G') I.down
    have e₂ := psum_hom (preHom H) (x3 G) I.down
    have e₃ : (fun i => pushHom gp Y (x3 G' i)) = fun i => preHom H (x3 G i) :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, H]
    exact congrArg (fun q => q.left) (e₁.trans ((congrArg (fun q => psum G q I.down) e₃).trans e₂.symm))
  obtain ⟨a, ha, hv⟩ := GlobalTheory.ConstFam.exists_gen_through (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (h := H.left) hw L.isLB L'.isLB hψ c.t c.isGen
  have ev : ∀ {T : Over S'} (z : T.left) {J J'}, Good L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G',
      cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * val a (lift x (lift y u)).left z J' := by
    intro T z J J' hJ hJ' x y u
    have e := hv _ (lift x (lift y u)).left z J J' hJ hJ'
    refine Eq.trans ?_ (e.trans (congrArg (· * _) (prod_cub x y u (GlobalTheory.ConstFam.wVal w z J J'))))
    let R : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := (Over.map f).map (lift x (lift y u))
    have p : ∀ q : Y ⟶ G', R ≫ pushHom gp Y q = pushHom gp T (lift x (lift y u) ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have q : lift (pushHom gp T x) (lift (pushHom gp T y) (pushHom gp T u)) = R ≫ H := by
      simp only [H, comp_lift, p]
      simp [x3]
    exact congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) (congrArg (fun q => q.left) q)
  have sj : Function.Surjective (Y.hom).appTop.hom := by
    have := surj_comp (surj_snd hG hA (G' ⊗ G')) (surj_comp (surj_snd hG hA G') (hG _ _ hA).2)
    rwa [Over.w, Over.w] at this
  have key := gen_unique (φ := thφ G' (x3 G')) (ε := thε) L'.isLB Y.hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left (Over.w _) sj ha c'.isGen
    (fun y I' hI' => by
      obtain ⟨I, hI⟩ := GlobalTheory.ConstFam.exists_good' L.isLB y
      have E := ev (T := 𝟙_ (Over S')) y hI hI' 1 1 1
      rw [map_one, (isCub_cubV c hI).face] at E
      refine Eq.trans ?_ ((isCub_cubV (T := 𝟙_ (Over S')) c' hI').face 1 1).symm
      have fin : ∀ {A U : Type} [Group A] [CommGroup U] (h : A → U) (b : U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * b → b = 1 := fun h b e => by
          simpa using e.symm
      exact fin (fun q : 𝟙_ (Over S') ⟶ G' => GlobalTheory.ConstFam.wVal w y I I' q.left) _ E) _
    (lift x (lift y u)).left z J' hJ'
  exact (ev z hJ hJ' x y u).trans (congrArg _ key)

theorem exists_cube_const {L : RigLB G} (c : CubicalStr G L) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (fr : ∀ a, LB.Gen (LB.LinComb L.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))) (hfr : ∀ a, (fr a).IsGen) (a a' a'' : Γ') :
    ∃ k : Γ(T.left, ⊤), ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
      (cubV c z J (ρ ≫ pt a) (ρ ≫ pt a') (ρ ≫ pt a'') * ((val (fr (a + a')) ρ.left z J * val (fr (a + a'')) ρ.left z J *
        val (fr (a' + a'')) ρ.left z J * val (fr 0) ρ.left z J) * (val (fr (a + a' + a'')) ρ.left z J *
          val (fr a) ρ.left z J * val (fr a') ρ.left z J * val (fr a'') ρ.left z J)⁻¹)).val = gs ρ.left z ⊤ k := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have g4 := fun b₁ b₂ b₃ b₄ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (hfr b₁) (hfr b₂)) (hfr b₃)) (hfr b₄)
  obtain ⟨k, hk⟩ := H1.exists_const L.L L.isLB (𝟙 T.left) (fun b => ⟨b, rfl⟩) _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen L.L (thφ G (x3 G)) thε c.t c.isGen
      (lift (pt a) (lift (pt a') (pt a''))).left)
      (mulGen_isGen _ _ _ _ _ _ _ (g4 (a + a') (a + a'') (a' + a'') 0)
        (invGen_isGen _ _ _ _ (g4 (a + a' + a'') a a' a'')))) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_cub (pt a) (pt a') (pt a'') h) rfl)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hadd, h0, zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨k, fun T' ρ z J hJ => ?_⟩
  have e := hk _ ρ.left z J hJ
  rw [Category.comp_id] at e
  refine Eq.trans (congrArg Units.val ?_) e
  have v4 := fun b₁ b₂ b₃ b₄ => (val_mul hJ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (fr b₁) (fr b₂)) (fr b₃)) (fr b₄)
    ρ.left).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_mul hJ _ _ _))))
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (v4 _ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (v4 _ _ _ _))))))).symm

end General

section Torsion

open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

theorem reg_cub {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {y : T.left} {J}
    (hJ : Good L.L y J) (m₁ m₂ m₃ : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (m₁ * m₂ * m₃) * (h (m₁ * m₂))⁻¹ * (h (m₁ * m₃))⁻¹ * (h (m₂ * m₃))⁻¹ * h m₁ * h m₂ *
      h m₃ * (h 1)⁻¹) (fun z => cubV c y J (ptSecT A z ≫ m₁) (ptSecT A z ≫ m₂) (ptSecT A z ≫ m₃)) :=
  ⟨_, _, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift m₁ (lift m₂ m₃)).left,
    pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub m₁ m₂ m₃ h, fun a => val_cub c (ptSecT A a) hJ _ _ _⟩

theorem cube_torsFrame_pow (hG : GlobalFnsSt) (P : PolAV S) [IsCommMonObj P.A] {rig : LB.Gen (P.L.pull (eSec P.A))}
    {hrig : rig.IsGen} (c : CubicalStr P.A ⟨P.L, rig, P.isLB, hrig⟩) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) {m : ℕ}
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1)))
    (hfr : ∀ a, IsTorsFrame P rig m (pt a) (fr a)) (a a' a'' : Γ') (z : T.left) (J) (hJ : Good P.L z J) :
    (cubV c z J (pt a) (pt a') (pt a'') * ((val (fr (a + a')) (𝟙 _) z J * val (fr (a + a'')) (𝟙 _) z J *
        val (fr (a' + a'')) (𝟙 _) z J * val (fr 0) (𝟙 _) z J) * (val (fr (a + a' + a'')) (𝟙 _) z J *
          val (fr a) (𝟙 _) z J * val (fr a') (𝟙 _) z J * val (fr a'') (𝟙 _) z J)⁻¹)) ^ (m ^ 2) = 1 := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  have rα := Reg.two (y := z) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  obtain ⟨p, hp, hp'⟩ : ∃ p : T ⊗ P.A ⟶ P.A, p ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ p = pt a :=
    ⟨fst T P.A ≫ pt a, by rw [← SymLiftOdd.comp_pow', (hfr a).1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  obtain ⟨q, hq, hq'⟩ : ∃ q : T ⊗ P.A ⟶ P.A, q ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ q = pt a' :=
    ⟨fst T P.A ≫ pt a', by rw [← SymLiftOdd.comp_pow', (hfr a').1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  have r := (((reg_cub c hJ p q (snd T P.A)).pow hJ (m ^ 2)).mul hJ
    (((((rα.pull hJ (p * q)).mul hJ (rα.pull hJ (p * snd T P.A))).mul hJ (rα.pull hJ (q * snd T P.A))).mul hJ
      (rα.pull hJ 1)).mul hJ ((((rα.pull hJ (p * q * snd T P.A)).mul hJ (rα.pull hJ p)).mul hJ (rα.pull hJ q)).mul hJ
        rα).inv)).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, mul_pow, hp, hq, one_pow, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (pt a'') 1
  simp only [MonObj.comp_mul, MonObj.comp_one, pt_snd, hp', hq', _root_.mul_one] at r
  rw [(isCub_cubV c hJ).face₃] at r
  have t := fun b => congrArg Additive.ofMul (torsFrame_pow hG P hα (hfr b) hJ)
  have t₁ := t (a + a' + a'')
  have t₂ := t (a + a')
  have t₃ := t (a + a'')
  have t₄ := t (a' + a'')
  have t₅ := t a
  have t₆ := t a'
  have t₇ := t a''
  have t₈ := t 0
  simp only [← hadd] at r
  rw [← h0] at r
  generalize val α (ptSecT P.A 1).left z J = e at t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
  apply Additive.ofMul.injective
  replace r := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at r t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ ⊢
  linear_combination (norm := module) r + t₂ + t₃ + t₄ + t₈ - t₁ - t₅ - t₆ - t₇

end Torsion

theorem exists_frame_cube_const : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro g n F W Z i X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.Poinc.PtAdd.x_add g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

end GlobalTheory.Poinc.CubeConst
