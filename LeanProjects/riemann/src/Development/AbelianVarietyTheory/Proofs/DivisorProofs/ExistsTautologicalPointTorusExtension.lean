import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NotExistsDataOfNotSymm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TautGt

open GlobalTheory.TChart.GensFrom in

theorem exists_gen_at {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) {T' : Over (Sp V)} (x y : T' ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = T'.hom ≫ spMap iw ≫ x₀.left)
    (hy : y.left ≫ β = T'.hom ≫ spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (𝟙 _) z J' = lamVal w (lift x y).left z J J' * val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = (T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = ((T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst, Category.assoc]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = ((T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd, Category.assoc]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (T'.hom ≫ spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (𝟙 T'.left) z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (𝟙 T'.left) z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z hJ
  have e2 := hva _ (𝟙 T'.left) z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  simp only [Category.id_comp] at e1 e2
  rw [e1, ← inv_inv (val τ₁ (T'.hom ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TautGt

noncomputable section
namespace GlobalTheory.TautGt

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem mult_alg {G : Type} [CommGroup G] (u₁ u₂ L L₁ L₂ t t₁ t₂ cD cT : G) (h1 : L * cD = L₁ * L₂ * cT)
    (h2 : t * cT = t₁ * t₂) : u₁ * u₂ * (L * t) * cD = u₁ * (L₁ * t₁) * (u₂ * (L₂ * t₂)) := by
  rw [eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def kU {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (x a : Fin r → ℤ) : Fˣ :=
  Units.mk0 (∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i x a)
    (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ((map_ne_zero _).2
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i))))

theorem kU_add {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (x x' a : Fin r → ℤ) : kU s hs ε F (x + x') a = kU s hs ε F x a * kU s hs ε F x' a := by
  apply Units.ext
  simp only [kU, Units.val_mk0, Units.val_mul, map_add, LinearMap.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => zpow_add₀ ((map_ne_zero _).2
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i))) _ _

theorem kU_zero {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (a : Fin r → ℤ) : kU s hs ε F 0 a = 1 := by
  apply Units.ext
  simp [kU]

end GlobalTheory.TautGt

open GlobalTheory.TautGt in

theorem GlobalTheory.TInj.exists_tautPt : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ g : GtPtF D F, TautPt T ω s ε n D e β ββ w F a g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF hs F _ _ a
  have hF' := hF
  obtain ⟨hpb, hsq, hw, hc, -⟩ := hF
  have hι : (toUnit (TF (R := V) F)).left = (TF (R := V) F).hom := rfl
  let bL : (TF (R := V) F).left ⟶ D.P.A.left :=
    hpb.1.lift ((TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left) (TF (R := V) F).hom (by
      rw [Category.assoc, Category.assoc, Over.w (T.c₀ a)]; rfl)
  let b : TF (R := V) F ⟶ D.P.A := Over.homMk bL (hpb.1.lift_snd _ _ _)
  have hb : b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left := hpb.1.lift_fst _ _ _
  have hx : ∀ χ : D.X, (DegPre.cF D F χ).left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ ((n : ℤ) • e χ)).left :=
    fun χ => by
      show ((toUnit (TF (R := V) F)).left ≫ (D.c χ).left) ≫ β = _
      rw [Category.assoc, hc χ, hι]
  have key := fun χ : D.X => exists_gen_at T.M.isLB D.P.isLB ω hsq w hw (DegPre.cF D F χ) b
    (T.c₀ ((n : ℤ) • e χ)) (T.c₀ a) (hx χ) hb (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  have hval : ∀ χ z J J', Good T.M.L z J → Good D.P.L z J' →
      val (scaleGen (τ χ) (unitOn (kU s hs ε F (e χ) a))) (𝟙 _) z J' =
        gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn (kU s hs ε F (e χ) a)) *
          (lamVal w (lift (DegPre.cF D F χ) b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J) := fun χ z J J' hJ hJ' => by
    rw [val_scaleGen _ _ _ _ hJ', hτv χ z J J' hJ hJ']
  have hτ0 : ∀ y J, Good T.M.L y J → val (T.τ₀ 0 a) ((TF (R := V) F).hom ≫ spMap ω) y J = 1 := fun y J hJ => by
    have C : LB.Gen.Corr T.M.L _ _ _ _ (T.τ₀ 0 a) (LB.oneGen T.M.L) := corr_of_val T.M.isLB fun y J hJ =>
      (show val (T.τ₀ 0 a) (𝟙 _) y J = 1 by
        have h := T.τ₀_add 0 0 a y J hJ
        have f : cubV T.cub y J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
          rw [TautBase.c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
        rw [f, _root_.mul_one, add_zero] at h
        exact mul_eq_left.1 h.symm).trans (val_one _).symm
    exact (val_corr hJ C _).trans (val_one _)
  have hc0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have hcF0 : DegPre.cF D F 0 = 1 := by
    show toUnit _ ≫ D.c 0 = 1
    rw [hc0, MonObj.comp_one]
  have hcF : ∀ χ χ', DegPre.cF D F (χ + χ') = DegPre.cF D F χ * DegPre.cF D F χ' := fun χ χ' => by
    show toUnit _ ≫ D.c (χ + χ') = _
    rw [D.c_add]
    exact MonObj.comp_mul _ _ _
  have unitOn_mul : ∀ k k' : Fˣ, unitOn (k * k') = unitOn k * unitOn k' := fun k k' => map_mul _ _ _
  refine ⟨{ b := b
            s := fun χ => scaleGen (τ χ) (unitOn (kU s hs ε F (e χ) a))
            isGen := fun χ => scaleGen_isGen D.P.isLB _ (hτg χ) _
            s_zero := ?_
            mult := ?_ }, hb, fun χ => ⟨kU s hs ε F (e χ) a, rfl, fun z J J' hJ hJ' => hval χ z J J' hJ hJ'⟩⟩
  · refine corr_of_val D.P.isLB fun y J' hJ' => ?_
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ y)
    refine (hval 0 y J J' hJ hJ').trans (Eq.trans ?_ (val_one _).symm)
    rw [map_zero e, kU_zero, smul_zero, hτ0 y J hJ, hcF0,
      (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) b y J J' hJ hJ').1,
      show unitOn (1 : Fˣ) = 1 from map_one _, map_one, _root_.mul_one, _root_.mul_one]
  · intro χ χ'
    refine corr_of_val D.P.isLB fun y J' hJ' => ?_
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ y)
    have hcub : val (DegPre.cubAt D F (DegPre.cF D F χ) (DegPre.cF D F χ') b) (𝟙 _) y J' =
        cubV D.cub y J' (DegPre.cF D F χ) (DegPre.cF D F χ') b := by
      unfold DegPre.cubAt
      refine (val_pull hJ' _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    let r := (TF (R := V) F).hom ≫ spMap ω
    let ρ := toUnit (Over.mk r)
    have W1 := (GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) (DegPre.cF D F χ') b
      (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ ((n : ℤ) • e χ')) (ρ ≫ T.c₀ a) ((hx χ).trans (Category.assoc _ _ _).symm)
      ((hx χ').trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm) y J J' hJ hJ').1
    have T1 : val (T.τ₀ ((n : ℤ) • e χ + (n : ℤ) • e χ') a) r y J *
        @id ((TF (R := V) F).left.presheaf.stalk y)ˣ
          (cubV T.cub y J (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ ((n : ℤ) • e χ')) (ρ ≫ T.c₀ a)) =
        val (T.τ₀ ((n : ℤ) • e χ) a) r y J * val (T.τ₀ ((n : ℤ) • e χ') a) r y J := by
      have C : LB.Gen.Corr T.M.L _ _ _ _
          (LB.mulGen T.M.L _ _ _ _ (T.τ₀ ((n : ℤ) • e χ + (n : ℤ) • e χ') a)
            (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t
              (lift (T.c₀ ((n : ℤ) • e χ)) (lift (T.c₀ ((n : ℤ) • e χ')) (T.c₀ a))).left))
          (LB.mulGen T.M.L _ _ _ _ (T.τ₀ ((n : ℤ) • e χ) a) (T.τ₀ ((n : ℤ) • e χ') a)) :=
        corr_of_val T.M.isLB fun y J hJ => by
          refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
          refine (congrArg (_ * ·) ((val_pull hJ _ _ _).trans ?_)).trans (T.τ₀_add _ _ a y J hJ)
          rw [Category.id_comp]
          rfl
      have h1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ C r).trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ h1
      exact congrArg (_ * ·) (val_cub T.cub ρ hJ _ _ _).symm
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    refine (congrArg₂ (· * ·) (hval (χ + χ') y J J' hJ hJ') hcub).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (hval χ y J J' hJ hJ') (hval χ' y J J' hJ hJ')).symm)
    rw [hcF, map_add e, kU_add, smul_add, unitOn_mul, map_mul]
    exact mult_alg _ _ _ _ _ _ _ _ _ _ W1 T1
