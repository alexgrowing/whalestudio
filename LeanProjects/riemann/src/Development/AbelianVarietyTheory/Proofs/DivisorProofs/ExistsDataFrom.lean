import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautBaseChangeTripleLiftLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.FromEx

section Base

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev Bp : Over (Sp V) := (Over.pullback (spMap iw)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T iw) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T iw) := (isAb_Bp T iw).comm

theorem cart : IsGrpPullback (Bp T iw) T.B (spMap iw) (pullback.fst T.B.hom (spMap iw)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T iw) T.B := cubeMapOf (cart T iw)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T iw).F).IsLB) (hr : ((cm T iw).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T iw) ((cm T iw).rigLB T.M hL hr), (cm T iw).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T iw).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T iw) (cm T iw) T.M T.cub

abbrev Mp : RigLB (Bp T iw) := (cm T iw).rigLB T.M (pullSt T iw).fst (pullSt T iw).snd.fst

abbrev cubP : CubicalStr (Bp T iw) (Mp T iw) := CubePf.cubical (cm T iw) T.M T.cub _ _

example : (Mp T iw).L = T.M.L.pull (pullback.fst T.B.hom (spMap iw)) := rfl

end Base

section Pts

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev push (Tt : Over (Sp V)) : (Tt ⟶ Bp T iw) →* (Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) := pushHom (cart T iw) Tt

theorem push_inj {Tt : Over (Sp V)} {x y : Tt ⟶ Bp T iw} (h : push T iw Tt x = push T iw Tt y) : x = y := by
  apply Over.OverMorphism.ext
  apply (cart T iw).1.hom_ext
  · exact congrArg (fun q => q.left) h
  · rw [Over.w x, Over.w y]

def pullPt {Tt : Over (Sp V)} (q : Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) : Tt ⟶ Bp T iw :=
  Over.homMk ((cart T iw).1.lift q.left Tt.hom (Over.w q)) ((cart T iw).1.lift_snd _ _ _)

theorem push_pullPt {Tt : Over (Sp V)} (q : Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) : push T iw Tt (pullPt T iw q) = q :=
  Over.OverMorphism.ext ((cart T iw).1.lift_fst _ _ _)

def cp (a : Fin T.r → ℤ) : 𝟙_ (Over (Sp V)) ⟶ Bp T iw := pullPt T iw (toUnit _ ≫ T.c₀ a)

theorem push_cp (a : Fin T.r → ℤ) : push T iw _ (cp T iw a) = toUnit _ ≫ T.c₀ a := push_pullPt T iw _

theorem cp_add (a a' : Fin T.r → ℤ) : cp T iw (a + a') = cp T iw a * cp T iw a' :=
  push_inj T iw (by rw [map_mul, push_cp, push_cp, push_cp, T.c₀_add, MonObj.comp_mul])

theorem left_of_push {Tt : Over (Sp V)} {z : Tt ⟶ Bp T iw} {z₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (h : push T iw Tt z = toUnit _ ≫ z₀) : z.left ≫ pullback.fst T.B.hom (spMap iw) = (Tt.hom ≫ spMap iw) ≫ z₀.left := by
  have := congrArg (fun q => q.left) h
  simp only [Over.comp_left, TautEx.toUnit_left] at this
  exact this

theorem lam_comm {Tt : Over (Sp V)} {x y : Tt ⟶ Bp T iw} {x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (hx : push T iw Tt x = toUnit _ ≫ x₀) (hy : push T iw Tt y = toUnit _ ≫ y₀) (k : Fin 4) :
    lamPts x y k ≫ pullback.fst T.B.hom (spMap iw) = (Tt.hom ≫ spMap iw) ≫ lamPts x₀ y₀ k := by
  fin_cases k
  · exact left_of_push T iw (by rw [map_mul, hx, hy, MonObj.comp_mul])
  · exact left_of_push T iw hx
  · exact left_of_push T iw hy
  · exact left_of_push T iw (by rw [map_one, MonObj.comp_one])

theorem push_pre {Tt Tt' : Over (Sp V)} (U : Tt' ⟶ Tt) {x : Tt ⟶ Bp T iw} {x₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (hx : push T iw Tt x = toUnit _ ≫ x₀) : push T iw Tt' (U ≫ x) = toUnit _ ≫ x₀ := by
  apply Over.OverMorphism.ext
  have := left_of_push T iw hx
  show (U ≫ x).left ≫ pullback.fst T.B.hom (spMap iw) = _
  rw [Over.comp_left, Over.comp_left, TautEx.toUnit_left, Category.assoc, this, ← Category.assoc, ← Category.assoc,
    Over.w U]
  rfl

end Pts

section Charts

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

open Classical in

def Jd {Tt : Over (Sp V)} (z : Tt.left) (J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι) :
    (Tt.left ⟶ T.B.left) → T.M.L.ι := fun χ =>
  if hχ : χ ≫ T.B.hom = Tt.hom ≫ spMap iw then J ((cart T iw).1.lift χ Tt.hom hχ) PUnit.unit
  else (exists_chart T.M.isLB (χ z)).choose

theorem Jd_eq {Tt : Over (Sp V)} (z : Tt.left) (J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι)
    (ψ : Tt.left ⟶ (Bp T iw).left) (hψ : ψ ≫ (Bp T iw).hom = Tt.hom) :
    Jd T iw z J (ψ ≫ pullback.fst T.B.hom (spMap iw)) = J ψ PUnit.unit := by
  have hχ : (ψ ≫ pullback.fst T.B.hom (spMap iw)) ≫ T.B.hom = Tt.hom ≫ spMap iw := by
    rw [Category.assoc, (cart T iw).1.w, ← Category.assoc, hψ]
  rw [Jd, dif_pos hχ]
  congr 1
  exact (cart T iw).1.hom_ext ((cart T iw).1.lift_fst _ _ _) (((cart T iw).1.lift_snd _ _ _).trans hψ.symm)

theorem Jd_good {Tt : Over (Sp V)} {z : Tt.left} {J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : Good T.M.L z (Jd T iw z J) := by
  intro χ
  by_cases hχ : χ ≫ T.B.hom = Tt.hom ≫ spMap iw
  · have := mem_pull.1 (hJ ((cart T iw).1.lift χ Tt.hom hχ))
    rw [Jd, dif_pos hχ]
    have h2 : ((cart T iw).1.lift χ Tt.hom hχ ≫ pullback.fst T.B.hom (spMap iw)) z ∈
        T.M.L.U (J ((cart T iw).1.lift χ Tt.hom hχ) PUnit.unit) := this
    rw [(cart T iw).1.lift_fst χ Tt.hom hχ] at h2
    exact h2
  · rw [Jd, dif_neg hχ]
    exact (exists_chart T.M.isLB (χ z)).choose_spec

theorem val_pullAlong {Tt : Over (Sp V)} {Y₀ Y : Scheme.{0}} {K : Type} [Fintype K]
    (h : Y ⟶ Y₀) (φ : K → (Y₀ ⟶ T.B.left)) (ε : K → ℤ) (ψ : K → (Y ⟶ (Bp T iw).left))
    (hψ : ∀ k, ψ k ≫ pullback.fst T.B.hom (spMap iw) = h ≫ φ k) (t : LB.Gen (LB.LinComb T.M.L φ ε)) (r : Tt.left ⟶ Y)
    (hw : ∀ k, r ≫ ψ k ≫ (Bp T iw).hom = Tt.hom) {z : Tt.left} {J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (spMap iw)) h φ ε ψ hψ t) r z J = val t (r ≫ h) z (Jd T iw z J) := by
  have hz := hJ.mem ψ r
  refine ((gm_res r z _ hz _).trans (gm_pull r h z _ (GeneratorPullback.pullAlong_le T.M.L _ h φ ψ hψ _ hz) _)).trans ?_
  refine (val_of t (r ≫ h) z (Jd T iw z J) _ fun k => ?_).symm
  rw [Category.assoc, ← hψ k, ← Category.assoc, Jd_eq T iw z J _ (by rw [Category.assoc, hw k])]

end Charts

section Tau

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev cK (x : Fin T.r → ℤ) : TK V ⟶ Bp T iw := toUnit _ ≫ cp T iw x

theorem push_cK (x : Fin T.r → ℤ) : push T iw _ (cK T iw x) = toUnit _ ≫ T.c₀ x := push_pre T iw _ (push_cp T iw x)

def uT (x y : Fin T.r → ℤ) : LB.Gen (LB.LinComb (Mp T iw).L (lamPts (cK T iw x) (cK T iw y)) negε) :=
  GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (spMap iw)) ((TK V).hom ≫ spMap iw) (lamPts (T.c₀ x) (T.c₀ y)) negε _
    (lam_comm T iw (push_cK T iw x) (push_cK T iw y)) (T.τ₀ x y)

theorem isGen_uT (x y : Fin T.r → ℤ) : (uT T iw x y).IsGen :=
  LBxP.isGen_pullAlong T.M.L _ _ _ _ _ _ (T.τ₀ x y) (T.τ₀_gen x y)

theorem val_uT (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (uT T iw x y) (𝟙 _) z J = val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) := by
  have h₂ := val_pullAlong T iw ((TK V).hom ≫ spMap iw) (lamPts (T.c₀ x) (T.c₀ y)) negε
    (lamPts (cK T iw x) (cK T iw y)) (lam_comm T iw (push_cK T iw x) (push_cK T iw y)) (T.τ₀ x y) (𝟙 _)
    (fun k => by rw [Category.id_comp]; exact TautEx.lamPts_w _ _ k) hJ
  rw [Category.id_comp] at h₂
  exact h₂

theorem uT_symm (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : val (uT T iw x y) (𝟙 _) z J = val (uT T iw y x) (𝟙 _) z J := by
  rw [val_uT T iw x y hJ, val_uT T iw y x hJ, val_corr (Jd_good T iw hJ) (corr_of_val T.M.isLB (T.τ₀_symm x y))]

theorem tautBaseChange_tripleLift_left (x x' y : Fin T.r → ℤ) :
    (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left ≫ (cm T iw).F3 =
      ((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left := by
  apply hom_ext_triple
  intro i
  have hL : (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left ≫ (x3 (Bp T iw) i).left =
      (lift (cK T iw x) (lift (cK T iw x') (cK T iw y)) ≫ x3 (Bp T iw) i).left := rfl
  have hR : (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left ≫ (x3 T.B i).left =
      (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y)) ≫ x3 T.B i).left := rfl
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, hL, Category.assoc ((TK V).hom ≫ spMap iw), hR]
  obtain ⟨e₀, e₁, e₂⟩ := TautEx.triple_lift_comp_projections (cK T iw x) (cK T iw x') (cK T iw y)
  obtain ⟨f₀, f₁, f₂⟩ := TautEx.triple_lift_comp_projections (T.c₀ x) (T.c₀ x') (T.c₀ y)
  match i with
  | 0 => rw [e₀, f₀]; exact left_of_push T iw (push_cK T iw x)
  | 1 => rw [e₁, f₁]; exact left_of_push T iw (push_cK T iw x')
  | 2 => rw [e₂, f₂]; exact left_of_push T iw (push_cK T iw y)

theorem uT_add (x x' y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (uT T iw (x + x') y) (𝟙 _) z J * cubV (cubP T iw) z J (cK T iw x) (cK T iw x') (cK T iw y) =
      val (uT T iw x y) (𝟙 _) z J * val (uT T iw x' y) (𝟙 _) z J := by
  have hc : cubV (cubP T iw) z J (cK T iw x) (cK T iw x') (cK T iw y) = val T.cub.t
      (((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left) z (Jd T iw z J) := by
    refine (val_pullAlong T iw (cm T iw).F3 (thφ T.B (x3 T.B)) thε (thφ (Bp T iw) (x3 (Bp T iw)))
      (fun I => (cm T iw).psum_comm I.down) T.cub.t (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left
      (fun I => ?_) hJ).trans ?_
    · show _ ≫ (psum _ _ _).left ≫ _ = _
      rw [Over.w, Over.w]
    · exact congrArg (fun r => val T.cub.t r z (Jd T iw z J)) (tautBaseChange_tripleLift_left T iw x x' y)
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (x + x') y)
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ x y) (T.τ₀ x' y)) (fun y₁ J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y₁ J') (Category.id_comp _)))) ((T.τ₀_add x x' y y₁ J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have hJd := Jd_good T iw hJ
  have e : val (T.τ₀ (x + x') y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) *
      val T.cub.t (((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left) z (Jd T iw z J) =
      val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) *
        val (T.τ₀ x' y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) :=
    (congrArg (_ * ·) (val_pull hJd _ _ _).symm).trans ((val_mul hJd _ _ _).symm.trans
      ((val_corr hJd corr _).trans (val_mul hJd _ _ _)))
  rw [val_uT T iw _ _ hJ, val_uT T iw _ _ hJ, val_uT T iw _ _ hJ, hc]
  exact e

end Tau

section Periods

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (hs : ∀ k, s k ≠ 0)
  (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ)

def kU (a b : Fin T.r → ℤ) : (FractionRing V)ˣ :=
  ∏ k, (Units.mk0 (algebraMap V (FractionRing V) (s k)) fun h =>
    hs k (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))) ^ ((n : ℤ) * ε k a b)

theorem kU_val (a b : Fin T.r → ℤ) :
    (kU T s hs ε n a b : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i a b) := by
  simp [kU]

theorem kU_symm (hε : ∀ k a b, ε k a b = ε k b a) (a b : Fin T.r → ℤ) : kU T s hs ε n a b = kU T s hs ε n b a := by
  simp only [kU, hε _ a b]

theorem kU_add (a a' b : Fin T.r → ℤ) : kU T s hs ε n (a + a') b = kU T s hs ε n a b * kU T s hs ε n a' b := by
  simp only [kU, ← Finset.prod_mul_distrib, ← zpow_add, map_add, LinearMap.add_apply, mul_add]

def tauF (a b : Fin T.r → ℤ) :
    LB.Gen (LB.LinComb (Mp T iw).L (lamPts (cK T iw ((n : ℤ) • a)) (cK T iw ((n : ℤ) • b))) negε) :=
  TautEx.mulU (unitOn (kU T s hs ε n a b)) (uT T iw ((n : ℤ) • a) ((n : ℤ) • b))

theorem val_tauF (a b : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : val (tauF T iw s hs ε n a b) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitOn (kU T s hs ε n a b)) * val (uT T iw ((n : ℤ) • a) ((n : ℤ) • b)) (𝟙 _) z J :=
  TautEx.val_mulU (L := (Mp T iw).L) _ _ (𝟙 _) z J hJ

theorem tauF_add (a a' b : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (tauF T iw s hs ε n (a + a') b) (𝟙 _) z J *
        cubV (cubP T iw) z J (cK T iw ((n : ℤ) • a)) (cK T iw ((n : ℤ) • a')) (cK T iw ((n : ℤ) • b)) =
      val (tauF T iw s hs ε n a b) (𝟙 _) z J * val (tauF T iw s hs ε n a' b) (𝟙 _) z J := by
  have h := uT_add T iw ((n : ℤ) • a) ((n : ℤ) • a') ((n : ℤ) • b) hJ
  rw [← smul_add] at h
  rw [val_tauF T iw s hs ε n _ _ hJ, val_tauF T iw s hs ε n _ _ hJ, val_tauF T iw s hs ε n _ _ hJ, kU_add,
    TautEx.unitOn_mul, map_mul]
  exact TautEx.alg_step h

theorem pGen_Mp : PGen (L := T.M.L) (F := pullback.fst T.B.hom (spMap iw)) (CubePf.idIsoL (Mp T iw).L) :=
  (isGen_iff _).1 (CubePf.idIsoL_isGen (Mp T iw).isLB)

def dataF (hε : ∀ k a b, ε k a b = ε k b a) : Data V where
  B := Bp T iw
  isAb := isAb_Bp T iw
  g := T.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange T.g).of_isPullback (IsPullback.of_hasPullback _ _)
    T.smoothDim
  M := Mp T iw
  cub := cubP T iw
  ample := relAmple_pull (cart T iw).1 T.M.isLB (Mp T iw).isLB (pGen_Mp T iw) ⊤ (isAffineOpen_top _) (fun _ => trivial)
    T.ample
  ktriv := kTriv_pull (cart T iw) T.M.isLB (Mp T iw).isLB (pGen_Mp T iw) T.ktriv
  X := Fin T.r → ℤ
  c a := cp T iw ((n : ℤ) • a)
  c_add a a' := by rw [smul_add]; exact cp_add T iw _ _
  tau := tauF T iw s hs ε n
  tau_gen a b := TautEx.isGen_mulU _ (isGen_uT T iw _ _)
  tau_symm a b _ _ hJ := by
    rw [val_tauF T iw s hs ε n a b hJ, val_tauF T iw s hs ε n b a hJ, kU_symm T s hs ε n hε a b, uT_symm T iw _ _ hJ]
  tau_add a a' b _ _ hJ := tauF_add T iw s hs ε n a a' b hJ

end Periods

section abelian₂

theorem gm_swap {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j : L.ι} (hi : f y ∈ L.U i)
    (hj : f y ∈ L.U j) : gm f y _ (L.g i j) = (gm f y _ (L.g j i))⁻¹ :=
  eq_inv_of_mul_eq_one_left ((gm_cocycle hL f y hi hj hi).trans (gm_self hL f y hi))

theorem gw_idIsoL {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (j : L.ι) (k : PUnit → L.ι)
    (hj : F (f y) ∈ L.U j) (hk : F (f y) ∈ L.U (k PUnit.unit)) :
    gw (L := L) (F := F) (CubePf.idIsoL (L.pull F)) f y j k = gm (f ≫ F) y _ (L.g j (k PUnit.unit)) := by
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j (k PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U k from ⟨mem_pull.2 hj, mem_pull.2 hk⟩) _).trans
    (gm_pull f F y (L.U j ⊓ L.U (k PUnit.unit)) (show F (f y) ∈ L.U j ⊓ L.U (k PUnit.unit) from ⟨hj, hk⟩) _)

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev vId : LB.Iso (Mp T iw).L (T.M.L.pull (pullback.fst T.B.hom (spMap iw))) := CubePf.idIsoL (Mp T iw).L

abbrev wLam : LB.Iso (abelian₂ (Bp T iw) (Mp T iw).L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf (cart T iw))) :=
  GlobalTheory.HalfBC.lamIso (cart T iw) (vId T iw)

theorem isGen_wLam : (wLam T iw).IsGen :=
  GlobalTheory.HalfBC.isGen_lamIso _ _ ((isGen_iff _).2 (pGen_Mp T iw))

theorem val_trans (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ T.B.left) → T.M.L.ι}
    {J' : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι} (hJ : Good T.M.L z J) (hJ' : Good (Mp T iw).L z J') :
    val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J') =
      lamVal (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z J J' * val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z J := by
  have hJd := Jd_good T iw hJ'
  have mJ : ∀ q : (TK V).left ⟶ (Bp T iw).left, pullback.fst T.B.hom (spMap iw) (q z) ∈
      T.M.L.U (J (q ≫ pullback.fst T.B.hom (spMap iw))) := fun q => hJ (q ≫ pullback.fst T.B.hom (spMap iw))
  have mJ' : ∀ q : (TK V).left ⟶ (Bp T iw).left, pullback.fst T.B.hom (spMap iw) (q z) ∈
      T.M.L.U (J' q PUnit.unit) := fun q => mem_pull.1 (hJ' q)
  refine (gen_trans (T.τ₀_gen x y) ((TK V).hom ≫ spMap iw) z (hJd.mem _ _) (hJ.mem _ _)).trans
    (congrArg (· * _) ?_)
  let h : ((TK V).left ⟶ (Bp T iw).left) → ((TK V).left.presheaf.stalk z)ˣ := fun q =>
    gm (q ≫ pullback.fst T.B.hom (spMap iw)) z _
      (T.M.L.g (J (q ≫ pullback.fst T.B.hom (spMap iw))) (J' q PUnit.unit))
  have h₁ : trF (lamPts (T.c₀ x) (T.c₀ y)) negε ((TK V).hom ≫ spMap iw) z
      (fun k => Jd T iw z J' (((TK V).hom ≫ spMap iw) ≫ lamPts (T.c₀ x) (T.c₀ y) k))
      (fun k => J (((TK V).hom ≫ spMap iw) ≫ lamPts (T.c₀ x) (T.c₀ y) k)) =
      ∏ k, (h (lamPts (cK T iw x) (cK T iw y) k))⁻¹ ^ negε k := by
    refine Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) ?_
    have e₁ := lam_comm T iw (push_cK T iw x) (push_cK T iw y) k
    beta_reduce
    rw [← e₁, Jd_eq T iw z J' _ (TautEx.lamPts_w _ _ k)]
    exact gm_swap T.M.isLB (lamPts (cK T iw x) (cK T iw y) k ≫ pullback.fst T.B.hom (spMap iw)) z
      (mJ' (lamPts (cK T iw x) (cK T iw y) k)) (mJ (lamPts (cK T iw x) (cK T iw y) k))
  have h₂ : ∏ k, (h (lamPts (cK T iw x) (cK T iw y) k))⁻¹ ^ negε k =
      h (cK T iw x * cK T iw y).left * (h (cK T iw x).left)⁻¹ * (h (cK T iw y).left)⁻¹ *
        h (1 : TK V ⟶ Bp T iw).left := by
    simpa using Wit.prod_neg_lamPts (cK T iw x) (cK T iw y) h
  have h₃ : lamVal (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z J J' =
      ∏ I, h ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ^ GlobalTheory.PrimCocycle.lamε I := by
    have e : (fun I => J ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.HalfBC.sqOf (cart T iw) ≫
        GlobalTheory.PrimCocycle.lamφ T.B I)) = fun I => J (((lift (cK T iw x) (cK T iw y)).left ≫
          GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ≫ pullback.fst T.B.hom (spMap iw)) :=
      funext fun I => by rw [GlobalTheory.HalfBC.sqOf_lamφ, Category.assoc]
    show gw (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z
      (fun I => J ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.HalfBC.sqOf (cart T iw) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
      (fun I => J' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I)) = _
    rw [e, GlobalTheory.HalfBC.gw_lamIso (cart T iw) (vId T iw) (lift (cK T iw x) (cK T iw y)).left z
      (fun I => J (((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ≫
        pullback.fst T.B.hom (spMap iw)))
      (fun I => J' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (fun I => mJ ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (fun I => hJ' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))]
    refine Finset.prod_congr rfl fun I _ => congrArg (· ^ GlobalTheory.PrimCocycle.lamε I) ?_
    exact gw_idIsoL ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) z _ _
      (mJ ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (mJ' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
  refine h₁.trans (h₂.trans ?_)
  rw [h₃, GlobalTheory.PrimCocycle.prod_lam]

end abelian₂

theorem exists_dataFrom : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), (∀ k, s k ≠ 0) → (∀ k a b, ε k a b = ε k b a) →
      ∃ (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e := by
  intro o W V _ _ _ _ _ T iw I _ s ε n hs hε
  refine ⟨dataF T iw s hs ε n hε, AddEquiv.refl _, pullback.fst T.B.hom (spMap iw), GlobalTheory.HalfBC.sqOf (cart T iw),
    wLam T iw, cart T iw, GlobalTheory.HalfBC.isSquare_sqOf (cart T iw), isGen_wLam T iw, fun a => ?_,
    fun a b => ⟨kU T s hs ε n a b, kU_val T s hs ε n a b, fun z J J' hJ hJ' => ?_⟩⟩
  · exact (left_of_push T iw (push_cp T iw _)).trans (by rw [TautEx.unit_hom]; simp <;> rfl)
  · exact (val_tauF T iw s hs ε n a b hJ').trans
      (congrArg _ ((val_uT T iw _ _ hJ').trans (val_trans T iw _ _ hJ hJ')))

end GlobalTheory.TChart.FromEx
