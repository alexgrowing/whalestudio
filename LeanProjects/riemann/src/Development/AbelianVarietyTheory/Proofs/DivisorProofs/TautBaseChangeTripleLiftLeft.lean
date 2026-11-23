import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautEx

instance isDomain_mvPowerSeries (N : ℕ) (W : Type) [CommRing W] [IsDomain W] : IsDomain (MvPowerSeries (Fin N) W) :=
  NoZeroDivisors.to_isDomain _

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

section Gen

variable {Y : Scheme.{0}} {M : LB Y}

def mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

theorem gm_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {y : Y} {i : M.ι} (h : y ∈ M.U i) :
    gm (𝟙 Y) y (M.U i) ((mulU u t).s i) = gm (𝟙 Y) y ⊤ u * gm (𝟙 Y) y (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res (𝟙 Y) y _ h _))

theorem isGen_mulU (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (mulU u t).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have e := congrArg (gm (𝟙 Y) x _) (ht i j)
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx] at e
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx, gm_mulU u t hx.1, gm_mulU u t hx.2, e]
  exact mul_left_comm _ _ _

variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem val_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hJ : Good L z J) : val (mulU u t) r z J = gm r z ⊤ u * val t r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

end Gen

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev fC : Sp (MvPowerSeries (Fin N) W) ⟶ Sp W := spMap MvPowerSeries.C

abbrev Bp : Over (Sp (MvPowerSeries (Fin N) W)) := (Over.pullback (fC (W := W) N)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T N) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T N) := (isAb_Bp T N).comm

theorem cart : IsGrpPullback (Bp T N) T.B (fC N) (pullback.fst T.B.hom (fC N)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T N) T.B := cubeMapOf (cart T N)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T N).F).IsLB) (hr : ((cm T N).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T N) ((cm T N).rigLB T.M hL hr), (cm T N).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T N).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T N) (cm T N) T.M T.cub

abbrev Mp : RigLB (Bp T N) := (cm T N).rigLB T.M (pullSt T N).fst (pullSt T N).snd.fst

abbrev cubP : CubicalStr (Bp T N) (Mp T N) := CubePf.cubical (cm T N) T.M T.cub _ _

example : (Mp T N).L = T.M.L.pull (pullback.fst T.B.hom (fC N)) := rfl
example : (cubP T N).t = (cm T N).thetaPull T.M.L T.cub.t := rfl

end Base

section Pts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev push (Tt : Over (Sp (MvPowerSeries (Fin N) W))) :
    (Tt ⟶ Bp T N) →* (Over.mk (Tt.hom ≫ fC N) ⟶ T.B) := pushHom (cart T N) Tt

theorem push_left {Tt : Over (Sp (MvPowerSeries (Fin N) W))} (x : Tt ⟶ Bp T N) :
    (push T N Tt x).left = x.left ≫ pullback.fst T.B.hom (fC N) := rfl

theorem push_inj {Tt : Over (Sp (MvPowerSeries (Fin N) W))} {x y : Tt ⟶ Bp T N} (h : push T N Tt x = push T N Tt y) :
    x = y := by
  apply Over.OverMorphism.ext
  apply (cart T N).1.hom_ext
  · exact congrArg (fun q => q.left) h
  · rw [Over.w x, Over.w y]

def pullPt {Tt : Over (Sp (MvPowerSeries (Fin N) W))} (q : Over.mk (Tt.hom ≫ fC N) ⟶ T.B) : Tt ⟶ Bp T N :=
  Over.homMk ((cart T N).1.lift q.left Tt.hom (Over.w q)) ((cart T N).1.lift_snd _ _ _)

theorem push_pullPt {Tt : Over (Sp (MvPowerSeries (Fin N) W))} (q : Over.mk (Tt.hom ≫ fC N) ⟶ T.B) :
    push T N Tt (pullPt T N q) = q :=
  Over.OverMorphism.ext ((cart T N).1.lift_fst _ _ _)

def cp (a : Fin T.r → ℤ) : 𝟙_ (Over (Sp (MvPowerSeries (Fin N) W))) ⟶ Bp T N := pullPt T N (toUnit _ ≫ T.c₀ a)

theorem push_cp (a : Fin T.r → ℤ) : push T N _ (cp T N a) = toUnit _ ≫ T.c₀ a := push_pullPt T N _

theorem cp_add (a a' : Fin T.r → ℤ) : cp T N (a + a') = cp T N a * cp T N a' :=
  push_inj T N (by rw [map_mul, push_cp, push_cp, push_cp, T.c₀_add, MonObj.comp_mul])

theorem left_of_push {Tt : Over (Sp (MvPowerSeries (Fin N) W))} {z : Tt ⟶ Bp T N} {z₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (h : push T N Tt z = toUnit _ ≫ z₀) : z.left ≫ pullback.fst T.B.hom (fC N) = (Tt.hom ≫ fC N) ≫ z₀.left := by
  have := congrArg (fun q => q.left) h
  simp only [Over.comp_left, toUnit_left] at this
  exact this

theorem lam_comm {Tt : Over (Sp (MvPowerSeries (Fin N) W))} {x y : Tt ⟶ Bp T N} {x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (hx : push T N Tt x = toUnit _ ≫ x₀) (hy : push T N Tt y = toUnit _ ≫ y₀) (k : Fin 4) :
    lamPts x y k ≫ pullback.fst T.B.hom (fC N) = (Tt.hom ≫ fC N) ≫ lamPts x₀ y₀ k := by
  fin_cases k
  · exact left_of_push T N (by rw [map_mul, hx, hy, MonObj.comp_mul])
  · exact left_of_push T N hx
  · exact left_of_push T N hy
  · exact left_of_push T N (by rw [map_one, MonObj.comp_one])

theorem push_pre {Tt Tt' : Over (Sp (MvPowerSeries (Fin N) W))} (U : Tt' ⟶ Tt) {x : Tt ⟶ Bp T N}
    {x₀ : 𝟙_ (Over (Sp W)) ⟶ T.B} (hx : push T N Tt x = toUnit _ ≫ x₀) : push T N Tt' (U ≫ x) = toUnit _ ≫ x₀ := by
  apply Over.OverMorphism.ext
  have := left_of_push T N hx
  rw [push_left, Over.comp_left, Over.comp_left, toUnit_left, Category.assoc, this, ← Category.assoc, ← Category.assoc,
    Over.w U]
  rfl

theorem lamPts_w {S : Scheme.{0}} {G Tt : Over S} [GrpObj G] (x y : Tt ⟶ G) (k : Fin 4) :
    lamPts x y k ≫ G.hom = Tt.hom := by
  fin_cases k <;> simp [lamPts]

theorem unit_hom (S : Scheme.{0}) : (𝟙_ (Over S)).hom = 𝟙 S := rfl

end Pts

section Periods

variable (W : Type) [CommRing W] [IsDomain W] (N : ℕ)

theorem coordT_ne_zero (m : ℕ) (k : Fin N) : Taut.coordT W m N k ≠ 0 := by
  unfold Taut.coordT
  split_ifs
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single k 1)) h
    simp at this
  · intro h
    have := congrArg MvPowerSeries.constantCoeff h
    simp at this

def kU (m n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) :
    (FractionRing (MvPowerSeries (Fin N) W))ˣ :=
  ∏ k, (Units.mk0 (algebraMap (MvPowerSeries (Fin N) W) (FractionRing (MvPowerSeries (Fin N) W)) (Taut.coordT W m N k))
    fun h => coordT_ne_zero W N m k (IsFractionRing.injective _ (FractionRing (MvPowerSeries (Fin N) W))
      (h.trans (map_zero _).symm))) ^ ((n : ℤ) * ε k a b)

theorem kU_val (m n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) :
    (kU W N m n r ε a b : FractionRing (MvPowerSeries (Fin N) W)) = Taut.perFactor W m N n r ε a b := by
  simp [kU, Taut.perFactor]

theorem kU_symm (m n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (hε : ∀ k a b, ε k a b = ε k b a)
    (a b : Fin r → ℤ) : kU W N m n r ε a b = kU W N m n r ε b a := by
  simp only [kU, hε _ a b]

theorem kU_add (m n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a a' b : Fin r → ℤ) :
    kU W N m n r ε (a + a') b = kU W N m n r ε a b * kU W N m n r ε a' b := by
  simp only [kU, ← Finset.prod_mul_distrib, ← zpow_add, map_add, LinearMap.add_apply, mul_add]

end Periods

section Charts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

open Classical in

def Jd {Tt : Over (Sp (MvPowerSeries (Fin N) W))} (z : Tt.left) (J : (Tt.left ⟶ (Bp T N).left) → PUnit → T.M.L.ι) :
    (Tt.left ⟶ T.B.left) → T.M.L.ι := fun χ =>
  if hχ : χ ≫ T.B.hom = Tt.hom ≫ fC N then J ((cart T N).1.lift χ Tt.hom hχ) PUnit.unit
  else (exists_chart T.M.isLB (χ z)).choose

theorem Jd_eq {Tt : Over (Sp (MvPowerSeries (Fin N) W))} (z : Tt.left) (J : (Tt.left ⟶ (Bp T N).left) → PUnit → T.M.L.ι)
    (ψ : Tt.left ⟶ (Bp T N).left) (hψ : ψ ≫ (Bp T N).hom = Tt.hom) :
    Jd T N z J (ψ ≫ pullback.fst T.B.hom (fC N)) = J ψ PUnit.unit := by
  have hχ : (ψ ≫ pullback.fst T.B.hom (fC N)) ≫ T.B.hom = Tt.hom ≫ fC N := by
    rw [Category.assoc, (cart T N).1.w, ← Category.assoc, hψ]
  rw [Jd, dif_pos hχ]
  congr 1
  exact (cart T N).1.hom_ext ((cart T N).1.lift_fst _ _ _) (((cart T N).1.lift_snd _ _ _).trans hψ.symm)

theorem Jd_good {Tt : Over (Sp (MvPowerSeries (Fin N) W))} {z : Tt.left} {J : (Tt.left ⟶ (Bp T N).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T N).L z J) : Good T.M.L z (Jd T N z J) := by
  intro χ
  by_cases hχ : χ ≫ T.B.hom = Tt.hom ≫ fC N
  · have := mem_pull.1 (hJ ((cart T N).1.lift χ Tt.hom hχ))
    rw [Jd, dif_pos hχ]
    have h2 : ((cart T N).1.lift χ Tt.hom hχ ≫ pullback.fst T.B.hom (fC N)) z ∈
        T.M.L.U (J ((cart T N).1.lift χ Tt.hom hχ) PUnit.unit) := this
    rw [(cart T N).1.lift_fst χ Tt.hom hχ] at h2
    exact h2
  · rw [Jd, dif_neg hχ]
    exact (exists_chart T.M.isLB (χ z)).choose_spec

theorem val_pullAlong {Tt : Over (Sp (MvPowerSeries (Fin N) W))} {Y₀ Y : Scheme.{0}} {K : Type} [Fintype K]
    (h : Y ⟶ Y₀) (φ : K → (Y₀ ⟶ T.B.left)) (ε : K → ℤ) (ψ : K → (Y ⟶ (Bp T N).left))
    (hψ : ∀ k, ψ k ≫ pullback.fst T.B.hom (fC N) = h ≫ φ k) (t : LB.Gen (LB.LinComb T.M.L φ ε)) (r : Tt.left ⟶ Y)
    (hw : ∀ k, r ≫ ψ k ≫ (Bp T N).hom = Tt.hom) {z : Tt.left} {J : (Tt.left ⟶ (Bp T N).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T N).L z J) :
    val (GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (fC N)) h φ ε ψ hψ t) r z J = val t (r ≫ h) z (Jd T N z J) := by
  have hz := hJ.mem ψ r
  refine ((gm_res r z _ hz _).trans (gm_pull r h z _ (GeneratorPullback.pullAlong_le T.M.L _ h φ ψ hψ _ hz) _)).trans ?_
  refine (val_of t (r ≫ h) z (Jd T N z J) _ fun k => ?_).symm
  rw [Category.assoc, ← hψ k, ← Category.assoc, Jd_eq T N z J _ (by rw [Category.assoc, hw k])]

end Charts

section Tau

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v := map_mul _ _ _

theorem triple_lift_comp_projections {S : Scheme.{0}} {G Tt : Over S} (x y w : Tt ⟶ G) :
    lift x (lift y w) ≫ x3 G 0 = x ∧ lift x (lift y w) ≫ x3 G 1 = y ∧ lift x (lift y w) ≫ x3 G 2 = w := by
  simp [x3]

theorem alg_step {G : Type} [CommGroup G] {g₁ g₂ v c a b : G} (e : v * c = a * b) :
    g₁ * g₂ * v * c = g₁ * a * (g₂ * b) := by
  rw [mul_assoc (g₁ * g₂), e, _root_.mul_mul_mul_comm]

abbrev cK (a : Fin T.r → ℤ) : TK (MvPowerSeries (Fin N) W) ⟶ Bp T N := toUnit _ ≫ cp T N a

theorem push_cK (a : Fin T.r → ℤ) : push T N _ (cK T N a) = toUnit _ ≫ T.c₀ a := push_pre T N _ (push_cp T N a)

def tauP (a b : Fin T.r → ℤ) : LB.Gen (LB.LinComb (Mp T N).L (lamPts (cK T N a) (cK T N b)) negε) :=
  mulU (unitOn (kU W N m n T.r ε a b)) (GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (fC N))
    ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) (lamPts (T.c₀ a) (T.c₀ b)) negε _
    (lam_comm T N (push_cK T N a) (push_cK T N b)) (T.τ₀ a b))

def uP (a b : Fin T.r → ℤ) : LB.Gen (LB.LinComb (Mp T N).L (lamPts (cp T N a) (cp T N b)) negε) :=
  GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (fC N)) ((𝟙_ (Over (Sp (MvPowerSeries (Fin N) W)))).hom ≫ fC N)
    (lamPts (T.c₀ a) (T.c₀ b)) negε _ (lam_comm T N (push_cp T N a) (push_cp T N b)) (T.τ₀ a b)

theorem isGen_tauP (a b : Fin T.r → ℤ) : (tauP T N m n ε a b).IsGen :=
  isGen_mulU _ (LBxP.isGen_pullAlong T.M.L _ _ _ _ _ _ (T.τ₀ a b) (T.τ₀_gen a b))

theorem val_tauP (a b : Fin T.r → ℤ) {z : (TK (MvPowerSeries (Fin N) W)).left}
    {J : ((TK (MvPowerSeries (Fin N) W)).left ⟶ (Bp T N).left) → PUnit → T.M.L.ι} (hJ : Good (Mp T N).L z J) :
    val (tauP T N m n ε a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (kU W N m n T.r ε a b)) *
      val (T.τ₀ a b) ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) z (Jd T N z J) := by
  have h₂ := val_pullAlong T N ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) (lamPts (T.c₀ a) (T.c₀ b)) negε
    (lamPts (cK T N a) (cK T N b)) (lam_comm T N (push_cK T N a) (push_cK T N b)) (T.τ₀ a b) (𝟙 _)
    (fun k => by rw [Category.id_comp]; exact lamPts_w _ _ k) hJ
  rw [Category.id_comp] at h₂
  exact (val_mulU (L := (Mp T N).L) (unitOn (kU W N m n T.r ε a b)) _ (𝟙 _) z J hJ).trans (congrArg _ h₂)

theorem tau_comm₂ (hε : ∀ k a b, ε k a b = ε k b a) (a b : Fin T.r → ℤ) {z : (TK (MvPowerSeries (Fin N) W)).left}
    {J : ((TK (MvPowerSeries (Fin N) W)).left ⟶ (Bp T N).left) → PUnit → T.M.L.ι} (hJ : Good (Mp T N).L z J) :
    val (tauP T N m n ε a b) (𝟙 _) z J = val (tauP T N m n ε b a) (𝟙 _) z J := by
  rw [val_tauP T N m n ε a b hJ, val_tauP T N m n ε b a hJ, kU_symm W N m n T.r ε hε a b,
    val_corr (Jd_good T N hJ) (corr_of_val T.M.isLB (T.τ₀_symm a b))]

theorem tautBaseChange_tripleLift_left (a a' b : Fin T.r → ℤ) :
    (lift (cK T N a) (lift (cK T N a') (cK T N b))).left ≫ (cm T N).F3 =
      ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) ≫ (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left := by
  apply hom_ext_triple
  intro i
  have hL : (lift (cK T N a) (lift (cK T N a') (cK T N b))).left ≫ (x3 (Bp T N) i).left =
      (lift (cK T N a) (lift (cK T N a') (cK T N b)) ≫ x3 (Bp T N) i).left := rfl
  have hR : (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left ≫ (x3 T.B i).left =
      (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b)) ≫ x3 T.B i).left := rfl
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, hL, Category.assoc ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N), hR]
  obtain ⟨e₀, e₁, e₂⟩ := triple_lift_comp_projections (cK T N a) (cK T N a') (cK T N b)
  obtain ⟨f₀, f₁, f₂⟩ := triple_lift_comp_projections (T.c₀ a) (T.c₀ a') (T.c₀ b)
  match i with
  | 0 => rw [e₀, f₀]; exact left_of_push T N (push_cK T N a)
  | 1 => rw [e₁, f₁]; exact left_of_push T N (push_cK T N a')
  | 2 => rw [e₂, f₂]; exact left_of_push T N (push_cK T N b)

theorem tau_add_left_mul_cube (a a' b : Fin T.r → ℤ) {z : (TK (MvPowerSeries (Fin N) W)).left}
    {J : ((TK (MvPowerSeries (Fin N) W)).left ⟶ (Bp T N).left) → PUnit → T.M.L.ι} (hJ : Good (Mp T N).L z J) :
    val (tauP T N m n ε (a + a') b) (𝟙 _) z J * cubV (cubP T N) z J (cK T N a) (cK T N a') (cK T N b) =
      val (tauP T N m n ε a b) (𝟙 _) z J * val (tauP T N m n ε a' b) (𝟙 _) z J := by
  have hc : cubV (cubP T N) z J (cK T N a) (cK T N a') (cK T N b) = val T.cub.t
      (((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) ≫ (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left) z (Jd T N z J) := by
    refine (val_pullAlong T N (cm T N).F3 (thφ T.B (x3 T.B)) thε (thφ (Bp T N) (x3 (Bp T N)))
      (fun I => (cm T N).psum_comm I.down) T.cub.t (lift (cK T N a) (lift (cK T N a') (cK T N b))).left
      (fun I => ?_) hJ).trans ?_
    · show _ ≫ (psum _ _ _).left ≫ _ = _
      rw [Over.w, Over.w]
    · exact congrArg (fun r => val T.cub.t r z (Jd T N z J)) (tautBaseChange_tripleLift_left T N a a' b)
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') b)
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a b) (T.τ₀ a' b)) (fun y J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y J') (Category.id_comp _)))) ((T.τ₀_add a a' b y J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have hJd := Jd_good T N hJ
  have e : val (T.τ₀ (a + a') b) ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) z (Jd T N z J) *
      val T.cub.t (((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) ≫ (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left) z
        (Jd T N z J) =
      val (T.τ₀ a b) ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) z (Jd T N z J) *
        val (T.τ₀ a' b) ((TK (MvPowerSeries (Fin N) W)).hom ≫ fC N) z (Jd T N z J) :=
    (congrArg (_ * ·) (val_pull hJd _ _ _).symm).trans ((val_mul hJd _ _ _).symm.trans
      ((val_corr hJd corr _).trans (val_mul hJd _ _ _)))
  rw [val_tauP T N m n ε _ _ hJ, val_tauP T N m n ε _ _ hJ, val_tauP T N m n ε _ _ hJ, hc, kU_add, unitOn_mul, map_mul]
  exact alg_step e

end Tau

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

theorem pGen_Mp : PGen (L := T.M.L) (F := pullback.fst T.B.hom (fC N)) (CubePf.idIsoL (Mp T N).L) :=
  (isGen_iff _).1 (CubePf.idIsoL_isGen (Mp T N).isLB)

def dataTaut (hε : ∀ k a b, ε k a b = ε k b a) : Data (MvPowerSeries (Fin N) W) where
  B := Bp T N
  isAb := isAb_Bp T N
  g := T.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange T.g).of_isPullback (IsPullback.of_hasPullback _ _)
    T.smoothDim
  M := Mp T N
  cub := cubP T N
  ample := relAmple_pull (cart T N).1 T.M.isLB (Mp T N).isLB (pGen_Mp T N) ⊤ (isAffineOpen_top _) (fun _ => trivial)
    T.ample
  ktriv := kTriv_pull (cart T N) T.M.isLB (Mp T N).isLB (pGen_Mp T N) T.ktriv
  X := Fin T.r → ℤ
  c := cp T N
  c_add := cp_add T N
  tau := tauP T N m n ε
  tau_gen := isGen_tauP T N m n ε
  tau_symm a b _ _ hJ := tau_comm₂ T N m n ε hε a b hJ
  tau_add a a' b _ _ hJ := tau_add_left_mul_cube T N m n ε a a' b hJ

end Main

end GlobalTheory.PolDeg.TautEx
