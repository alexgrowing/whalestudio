import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinearStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PsiPull
open GlobalTheory.UT.CoefBasic

section Base
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem val_eq_of_zero (hG : GlobalFnsSt) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φ' : K' → (D.P.A.left ⟶ D.P.A.left)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} {u' : LB.Gen (LB.LinComb D.P.L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good D.P.L y J → val u (eSec D.P.A) y J = val u' (eSec D.P.A) y J)
    {Z : Scheme.{0}} (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB hF u hu
  exact (hv _ r z J hJ).symm.trans (gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 ht hu' (fun y I hI => (hv _ _ y I hI).trans (h y I hI)) _ r z J hJ)

theorem Normd.val_zero {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J)
    (hJ : Good D.P.L z J) : val u (r ≫ eSec D.P.A) z J = 1 :=
  (val_pull hJ u (eSec D.P.A) r).symm.trans ((val_corr hJ hu.2 r).trans (val_one _))

theorem prod_O {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (p * cP D T χ).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four]
  show h (p * cP D T χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oinv {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (D.Oφ p χ i) ^ Oinvε i =
      (h (p * cP D T χ).left)⁻¹ * h (cP D T χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (p * cP D T χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h p.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_kap {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (a : D.P.A ⟶ D.P.A) (ν : ℕ) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (p.left ≫ (![𝟙 _, a.left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
      (![(ν : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ν] : Fin 3 → ℤ) i =
      h p.left ^ ν * (h (p ≫ a).left)⁻¹ * (h (1 : T ⟶ D.P.A).left * (h (1 : T ⟶ D.P.A).left ^ ν)⁻¹) := by
  rw [Fin.prod_univ_three]
  have e : p.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) p)
  show h (p.left ≫ 𝟙 _) ^ (ν : ℤ) * h (p ≫ a).left ^ (-((1 : ℕ) : ℤ)) *
    h (p.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (((1 : ℕ) : ℤ) - ν) = _
  rw [e, Category.comp_id, Nat.cast_one, zpow_sub, zpow_neg, zpow_one, zpow_one, zpow_natCast, zpow_natCast]

theorem val_twist_zero (hG : GlobalFnsSt) (a : D.P.A ⟶ D.P.A) {x : D.X} (hx : x = 0)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a 0)) (Sum.elim Oε Oinvε))) (hu : Normd u)
    {Z : Scheme.{0}} (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = 1 := by
  subst hx
  refine (val_eq_of_zero hG (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_)
    (u' := LB.oneGen D.P.L) hu.1
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    (fun y I hI => ?_) r z J hJ).trans (val_one _)
  · refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_O (𝟙 _) 0 h) (prod_Oinv a 0 h)).trans ?_
    rw [cPoint_zero]
    simp
  · have := Normd.val_zero hu (𝟙 _) y I hI
    rw [Category.id_comp] at this
    exact this.trans (val_one _).symm

theorem kappa_add (hG : GlobalFnsSt) (a : D.P.A ⟶ D.P.A) [IsMonHom a] {ν : ℕ} {y y' x : D.X} (hx : x = ν • y)
    (hc : D.c y' = D.c y ≫ a) (κ : LB.Gen (kapLB D a ν 1)) (hκ : Normd κ)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a y')) (Sum.elim Oε Oinvε))) (hu : Normd u)
    {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val κ (b * cP D T y).left z J * cubN (th D z J) ν 1 (cP D T y) b =
      val κ b.left z J * val κ (cP D T y).left z J * val u b.left z J := by
  subst hx
  have hc' : cP D D.P.A y' = cP D D.P.A y ≫ a := by rw [cP, hc, ← Category.assoc]; rfl
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : D.P.A ⟶ D.P.A) (cP D D.P.A y) (𝟙 D.P.A) ν
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ κ (𝟙 D.P.A * cP D D.P.A y).left) N) b.left z J =
        val κ (b * cP D T y).left z J * cubN (th D z J) ν 1 (cP D T y) b ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ κ (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)
        (LB.pullGen D.P.L _ _ κ (cP D D.P.A y).left)) u) b.left z J =
        val κ b.left z J * val κ (cP D T y).left z J * val u b.left z J := by
    intro T b z J hJ
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, vN T b z J hJ, ← Over.comp_left,
      ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP, Category.comp_id, MonObj.comp_one]
    exact ⟨rfl, rfl⟩
  rw [← (key b z J hJ).1, ← (key b z J hJ).2]
  refine val_eq_of_zero hG (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hκ.1 _) hN)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hκ.1 _)
      (pullGen_isGen _ _ _ _ hκ.1 _)) hu.1) (fun w I hI => ?_) _ z J hJ
  · refine Eq.trans (prod_sum₂ (K := Fin 3) (K' := Fin 8) (U := U) _ (prod_kap _ a ν h) rfl)
      (Eq.trans ?_ (prod_sum₂ (K := Fin 3 ⊕ Fin 3) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := U) _ (prod_kap _ a ν h) (prod_kap _ a ν h))
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_O (𝟙 _) (ν • y) h) (prod_Oinv a y' h))).symm)
    rw [MonObj.mul_comp, Category.id_comp, cPoint_nsmul, hc', mul_comm (𝟙 D.P.A) (cP D D.P.A y),
      mul_comm (𝟙 D.P.A) (cP D D.P.A y ^ ν)]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have C : IsCub (th D (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) w I) := isCub_cubV D.cub hI
    obtain ⟨k₁, k₂⟩ := key (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) w I hI
    have e₁ := Normd.val_zero hκ (𝟙_ (Over (Spec (CommRingCat.of R)))).hom w I hI
    have e₂ := Normd.val_zero hu (𝟙_ (Over (Spec (CommRingCat.of R)))).hom w I hI
    have e : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    rw [← e]
    refine k₁.trans (Eq.trans ?_ k₂.symm)
    rw [C.N_one, _root_.mul_one, _root_.one_mul]
    exact ((congrArg₂ (· * ·) (congrArg₂ (· * ·) e₁ rfl) e₂).trans (by rw [_root_.one_mul, _root_.mul_one])).symm

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem fe_zero (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (s : Fam D F k) (y : D.X) {x : D.X} (hx : x = k • y)
    (b : TF (R := R) F ⟶ D.P.A) (z : (TF (R := R) F).left) (J) (hJ : Good D.P.L z J) :
    sval (s.s x) (lift (𝟙 (TF (R := R) F)) b).left z J =
      sval (s.s 0) (lift (𝟙 (TF (R := R) F)) (b * cP D _ y)).left z J *
        (cubN (th D z J) k 1 (cP D _ y) b * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ
          (val (D.psi y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) ^ k).val := by
  obtain rfl : x = 0 + k • y := hx.trans (zero_add _).symm
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k y 0
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y 0 u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ
  have t : lift (𝟙 (TF (R := R) F)) b ≫ DegPre.trPt D F (cP D _ y) = lift (𝟙 (TF (R := R) F)) (b * cP D _ y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [lift_snd, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F (cP D _ y))).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
  have τ : val (D.tau y 0) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J = 1 := by
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 y
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (tau_symm (𝟙 (TF (R := R) F)) hJ _ _).trans (mul_eq_left.1 t.symm)
  rw [hv u hu hc _ _ z J hJ, trF_eq, ← Over.comp_left, t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp,
    val_famMult _ hJ, τ, cPoint_zero, C.face, inv_one, _root_.mul_one, _root_.one_mul] at e
  refine e.trans (congrArg (fun v : ((TF (R := R) F).left.presheaf.stalk z)ˣ => _ * (_ * v).val) ?_)
  rw [mul_pow]
  refine congrArg₂ (· * ·) (map_pow _ _ _) ((map_pow _ _ _).trans (congrArg (· ^ k) ?_))
  exact val_pull hJ _ _ _

end Base

theorem isUnit_gs {Y Z : Scheme.{0}} {U : Y.Opens} (a : Γ(Y, U)) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ Y.basicOpen a) :
    IsUnit (gs r z U a) := by
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
  exact hz

theorem isUnit_sval {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (σ : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ Y.basicOpen (σ.f j)) {J}
    (hJ : Good L z J) : IsUnit (sval σ r z J) :=
  isUnit_of_mul_isUnit_right ((congrArg IsUnit (sec_trans σ r z (Y.basicOpen_le _ hz) (hJ.mem φ r))).mp
    (isUnit_gs (σ.f j) r z hz))

section Torsion
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {D : DegPre R} {F : Type} [Field F] [IsAlgClosed F]
  [CharZero F] [Algebra (FractionRing R) F]

theorem exists_comp_eq (hL : Laws) (a : D.P.A ⟶ D.P.A) [IsMonHom a] {ν : ℕ} (hν : 1 ≤ ν) (κ : LB.Gen (kapLB D a ν 1))
    (hκ : κ.IsGen) {n : ℕ} (hn : 1 ≤ n) (hc : n.Coprime ν) (x : TF (R := R) F ⟶ D.P.A) (hx : x ^ n = 1) :
    ∃ b : TF (R := R) F ⟶ D.P.A, b ≫ a = x := by
  let φ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    MonoidHom.mk' (· ≫ a) fun x y => MonObj.mul_comp x y a
  have ker : ∀ x : TF (R := R) F ⟶ D.P.A, x ≫ a = 1 → x ^ ν = 1 := fun x hx => by
    have e : translPt D.P.A x ≫ a = snd _ _ ≫ a := by
      rw [show translPt D.P.A x = (fst _ _ ≫ x) * snd _ _ from rfl, MonObj.mul_comp, Category.assoc, hx,
        MonObj.comp_one, _root_.one_mul]
    obtain ⟨c, hc, -⟩ := exists_gen D.P.isLB
      (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A x).left]) (ε' := ![(ν : ℤ), -(ν : ℤ)]) (fun U _ h => by
        refine (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := U) _ (prod_kap (snd _ _) a ν h)
          (prod_neg _ _ (prod_kap (translPt D.P.A x) a ν h))).trans ?_
        rw [e]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
        abel)
      (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ κ (snd (TF (R := R) F) D.P.A).left)
        (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ κ (translPt D.P.A x).left)))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hκ _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hκ _)))
    exact (hL.kerPow _ D.P ν hν _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ c hc _⟩
  have card := (hL.mulN _ D.P n hn).2.2.2.2 F (jFK (R := R) F ≫ jK R) (Nat.cast_ne_zero.2 (by omega))
  have : Finite {x : TF (R := R) F ⟶ D.P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (card.trans_ne (pow_ne_zero _ (by omega)))
  let f : {x : TF (R := R) F ⟶ D.P.A // x ^ n = 1} → {x : TF (R := R) F ⟶ D.P.A // x ^ n = 1} := fun x =>
    ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩
  have inj : Function.Injective f := fun x y h => by
    have h₁ : φ (x.1 / y.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val h
    have h₂ : (x.1 / y.1) ^ n = 1 := by rw [div_pow, x.2, y.2, div_one]
    have h₃ := pow_gcd_eq_one.2 ⟨h₂, ker _ h₁⟩
    rw [hc, pow_one, div_eq_one] at h₃
    exact Subtype.ext h₃
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective inj ⟨x, hx⟩
  exact ⟨b.1, congrArg Subtype.val hb⟩

theorem exists_torsion_ne_zero (hL : Laws) {K : Type} [Fintype K] {φ : K → ((DegPre.BF D F).left ⟶ D.P.A.left)}
    {ε : K → ℤ} (σ : LB.Sec (LB.LinComb D.P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) {l : ℕ} (hl : 2 ≤ l) :
    ∃ (x : TF (R := R) F ⟶ D.P.A) (j : ℕ), x ^ l ^ j = 1 ∧
      ∀ z J, Good D.P.L z J → IsUnit (sval σ (lift (𝟙 (TF (R := R) F)) x).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hσ
  have hsm := D.P.isAb.smooth
  let p : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsReduced (DegPre.BF D F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  obtain ⟨P', g, hg, -, hmul, -⟩ := hL.polBaseChange _ _ (jFK (R := R) F ≫ jK R) D.P
  let e : P'.A.left ≅ (DegPre.BF D F).left := hg.flip.isoPullback
  let W := (DegPre.BF D F).left.basicOpen (σ.f j)
  have hW : (W : Set (DegPre.BF D F).left).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
    hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  obtain ⟨y, hy⟩ := hW
  obtain ⟨_, hq, hq'⟩ := (PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred F P' l hl
    (Nat.cast_ne_zero.2 (by omega))).inter_open_nonempty (e.hom ⁻¹ᵁ W) (e.hom ⁻¹ᵁ W).isOpen ⟨e.inv y, by
      show e.hom (e.inv y) ∈ W
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; exact hy⟩
  obtain ⟨x, ⟨m, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hq'
  let Φ : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ jFK (R := R) F ≫ jK R) ⟶ D.P.A) :=
    MonoidHom.mk' (fun x => toBase hg.w x) (hmul _)
  let ρ : TF (R := R) F ⟶ Over.mk (𝟙 _ ≫ jFK (R := R) F ≫ jK R) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  have er : (lift (𝟙 (TF (R := R) F)) (ρ ≫ Φ x)).left = x.left ≫ e.hom := by
    refine pullback.hom_ext ?_ ?_
    · refine (congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (ρ ≫ Φ x))).trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_fst).trans (Over.w x))).symm
    · refine (congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) F)) (ρ ≫ Φ x))).trans ?_
      exact (Category.id_comp _).trans
        ((Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_snd)).symm
  refine ⟨ρ ≫ Φ x, m, by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one], fun z J hJ => ?_⟩
  obtain rfl : z = q := pt_eq (R := R) (F := F) z q
  have hz : (lift (𝟙 (TF (R := R) F)) (ρ ≫ Φ x)).left z ∈ W := by rw [er]; exact hq
  exact isUnit_sval σ j _ z hz hJ

end Torsion

theorem exists_gen_flat {X X' Y : Scheme.{0}} {L : LB X} (f : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (a : LB.Gen (LB.LinComb (L.pull f) φ ε)) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε), b.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ f) j ≤ LB.wchart (L.pull f) φ (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_res (𝟙 Y) y (le j) hy.1 _).trans
    (gen_trans ha (𝟙 Y) y (le j hy.1) (le j' hy.2)))).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_linComb L (fun k => φ k ≫ f) ε (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le j') hy.2 _)))).symm)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) rfl
  exact gm_pull_g L f (𝟙 Y ≫ φ k) y _ _ (Set.mem_iInter.1 (le j hy.1) k) (Set.mem_iInter.1 (le j' hy.2) k)

theorem exists_normalised {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : T ⊗ A ⟶ A)
    (hm : (ptSecT A (1 : T ⟶ A)).left ≫ m.left = T.hom ≫ eSec A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T (a - b)) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, hm]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T (a - b))) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _)) (NormTheta.rigT_isGen hρ _)) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

section Unif
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_gen_generic {U : UnifPre I D A G} (E : EndU U) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![k', -k])) (hβ : β.IsGen)
    (T : Over (Spec (CommRingCat.of (FractionRing R)))) :
    ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd T A.A).left, (snd T A.A ≫ E.aA).left] ![k', -k]), α.IsGen := by
  obtain ⟨w, hw⟩ := U.ext
  let π : T ⊗ A.A ⟶ (Over.pullback (jK R)).obj G := snd T A.A ≫ U.gen.inv
  obtain ⟨a, ha, -⟩ := H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw)
    (K := Fin 2) ![𝟙 _, E.aG.left] ![π.left, (π ≫ (Over.pullback (jK R)).map E.aG).left] ![k', -k]
    (π.left ≫ pullback.fst G.hom (jK R)) (fun i => by
      fin_cases i
      · exact (Category.comp_id _).symm
      · exact (Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)) β hβ
  obtain ⟨b, hb⟩ := exists_gen_flat _ _ _ a ha
  have e₀ : π ≫ U.gen.hom = snd T A.A := by rw [Category.assoc, U.gen.inv_hom_id, Category.comp_id]
  have e₁ : (π ≫ (Over.pullback (jK R)).map E.aG) ≫ U.gen.hom = snd T A.A ≫ E.aA := by
    rw [Category.assoc, E.ext, ← Category.assoc, e₀]
  obtain ⟨α, hα, -⟩ := exists_gen A.isLB (φ' := ![(snd T A.A).left, (snd T A.A ≫ E.aA).left]) (ε' := ![k', -k])
    (fun V _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q : T ⊗ A.A ⟶ A.A => h q.left ^ k') e₀
      · exact congrArg (fun q : T ⊗ A.A ⟶ A.A => h q.left ^ (-k)) e₁) b hb
  exact ⟨α, hα⟩

end Unif

theorem exists_pull_val : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre),
    Function.Injective E.h → ∀ ν : ℕ, 1 ≤ ν →
    (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen) →
    ∀ κ : LB.Gen (kapLB D.toPre E.aB ν 1), Normd κ → ∀ s : Fam D.toPre F 1, ∃ s' : Fam D.toPre F ν,
      ∀ χ (b : TF (R := R) F ⟶ D.toPre.P.A) (z : (TF (R := R) F).left) J, Good D.toPre.P.L z J →
        sval (s'.s (E.h χ)) (lift (𝟙 (TF (R := R) F)) b).left z J * (rigV D.toPre (TF (R := R) F).hom z J).val =
          sval (s.s χ) (lift (𝟙 (TF (R := R) F)) (b ≫ E.aB)).left z J *
            (val (E.u χ) b.left z J * val κ b.left z J * rigV D.toPre (TF (R := R) F).hom z J ^ ν).val := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ E hE ν hν ⟨β, hβ⟩ κ hκ s
  have := E.homA
  obtain ⟨⟨ρ, hρ⟩, hn, -⟩ := EvalZero.value_at_origin hL R I hI D A G hG U F
  obtain ⟨w₀, hw₀⟩ := hn ρ hρ
  obtain ⟨α₀, hα₀⟩ := exists_gen_generic E _ _ β hβ (TFK (R := R) F)
  obtain ⟨α, hα, hαn⟩ := exists_normalised A.isLB hρ (snd (TFK (R := R) F) A.A ≫ E.aA) (by
    rw [← Over.comp_left, ptSecT, lift_snd_assoc, MonObj.one_comp]; rfl) _ _ α₀ hα₀
  have hB := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F
  obtain ⟨t, ht, -⟩ := (hB 1 le_rfl w₀ hw₀.1).2 s
  obtain ⟨t', htt⟩ := ThetaPtExist.exists_isTwistPull A.isLB (lift (fst _ _) (snd (TFK (R := R) F) A.A ≫ E.aA)) _
    (lift_snd _ _) _ _ α hα t
  obtain ⟨s', ht', -⟩ := (hB ν hν w₀ hw₀.1).1 t'
  have H := (T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hE ν 1 le_rfl hν ⟨β, hβ⟩).2 w₀ ρ hw₀ _ _ (lift_snd _ _) (lift_fst _ _)
    rfl α hα hαn t t' s s' ht ht' htt κ hκ
  refine ⟨s', fun χ b z J hJ => ?_⟩
  obtain ⟨g, rfl⟩ := (gt_onto_divisible_kernel hL R I hI D F).1 b
  obtain ⟨g', hg', -⟩ := (T.uniformizationEndomorphism_calculus hL R I hI D A G hG U F E E E).1 g
  obtain ⟨w', hw'⟩ := (coef_basic R D.toPre F ν g).1
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g'.b) (ε' := DegPre.lineε 1)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := V) _ (prod_line ν g.b h) (prod_kap g.b E.aB ν h)).trans ?_
      rw [prod_line, hg'.1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (pullGen_isGen _ _ _ _ hκ.1 _))
  have hww : ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J := fun z J hJ => by
    rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]
  have a₁ := isCoef_coef g hw' (E.h χ) s' z J hJ
  have a₂ := isCoef_coef g' hw χ s z J hJ
  rw [(H g g' hg' w' w hw' hw hww).1 χ] at a₁
  rw [← hww z J hJ, hg'.2 χ z J hJ, pow_one] at a₂
  rw [← hg'.1]
  refine (Units.mul_left_inj (val (g.s (E.h χ)) (𝟙 _) z J * val w' (𝟙 _) z J)).1 ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at a₂ ⊢
  linear_combination (rigV D.toPre (TF (R := R) F).hom z J).val ^ ν * a₂ -
    (rigV D.toPre (TF (R := R) F).hom z J).val * a₁

theorem alg_units {M : Type} [CommRing M] {s p q p' : M} (hs : IsUnit s) {r u u₀ k₀ k₁ kc N N₁ a a' : Mˣ} {ν : ℕ}
    (h₁ : p * r.val = q * (u * k₀ * r ^ ν).val) (h₂ : p' * r.val = s * (u₀ * k₁ * r ^ ν).val)
    (h₃ : p = p' * (N * (a * r) ^ ν).val) (h₄ : q = s * (N₁ * (a' * r) ^ 1).val) (h₅ : u₀ = 1) (h₆ : N₁ = 1)
    (h₇ : k₁ * N = k₀ * kc * u) : a' * r = a ^ ν * kc * r ^ ν := by
  obtain ⟨s, rfl⟩ := hs
  rw [h₃, h₄, mul_right_comm, h₂, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, Units.val_inj,
    h₅, h₆] at h₁
  apply Additive.ofMul.injective
  have b₁ := congrArg Additive.ofMul h₁
  have b₇ := congrArg Additive.ofMul h₇
  simp only [ofMul_mul, ofMul_pow, ofMul_one] at b₁ b₇ ⊢
  linear_combination (norm := module) b₇ - b₁

theorem psi_pull : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → Function.Injective E.h → ∀ ν : ℕ, 1 ≤ ν → (∀ y, E.h (E'.h y) = ν • y) → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen) → ∀ κ : LB.Gen (kapLB D.toPre E.aB ν 1), Normd κ → ∀ y (z : (TK R).left) J, Good D.toPre.P.L z J → val (D.toPre.psi (E'.h y)) (𝟙 _) z J * rigV D.toPre (TK R).hom z J = val (D.toPre.psi y) (𝟙 _) z J ^ ν * val κ (D.toPre.xK y) z J * rigV D.toPre (TK R).hom z J ^ ν := by
  intro hL _ _ _ _ R _ _ _ I hI D A G _ _ hG U F _ _ _ E E' hR hE ν hν hh hβ κ hκ y z J hJ
  have hGF := hL.1.globalFns
  have := hI.1
  have := E.homB
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hc := (T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL R I hI D A G hG U E E' hR).2.2.2 y
  have hc' : cP D.toPre (TF (R := R) F) (E'.h y) = cP D.toPre _ y ≫ E.aB := by rw [cP, hc, ← Category.assoc]; rfl
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D.toPre) (F := F) hGF hL.2.1.secTwist D.tau_bimult le_rfl 0
  obtain ⟨x, j, hx, hu⟩ := exists_torsion_ne_zero hL.1 (s.s 0) ((hs 0).2 ⟨0, by simp⟩) (l := ν + 1) (by omega)
  obtain ⟨b₁, rfl⟩ := exists_comp_eq hL.1 E.aB hν κ hκ.1 (Nat.one_le_pow _ _ (by omega))
    (Nat.Coprime.pow_left j (by simp)) x hx
  obtain ⟨b, rfl⟩ : ∃ b, b * cP D.toPre (TF (R := R) F) y = b₁ := ⟨_, inv_mul_cancel_right _ _⟩
  obtain ⟨s', hs'⟩ := exists_pull_val hL R I hI D A G hG U F E hE ν hν hβ κ hκ s
  have key : ∀ (z : (TF (R := R) F).left) J, Good D.toPre.P.L z J →
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi (E'.h y)) (jFK (R := R) F) z J) *
        rigV D.toPre (TF (R := R) F).hom z J =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi y) (jFK (R := R) F) z J) ^ ν *
        val κ (cP D.toPre (TF (R := R) F) y).left z J * rigV D.toPre (TF (R := R) F).hom z J ^ ν := by
    intro z J hJ
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have h₂ := hs' 0 (b * cP D.toPre _ y) z J hJ
    have h₄ := fe_zero hGF D.tau_bimult s (E'.h y) (one_nsmul _).symm (b ≫ E.aB) z J hJ
    rw [hc', ← MonObj.mul_comp] at h₄
    have e : ∀ χ, χ = 0 → ∀ r : (TF (R := R) F).left ⟶ _, sval (s'.s χ) r z J = sval (s'.s 0) r z J := by
      rintro _ rfl _; rfl
    rw [e _ (map_zero E.h)] at h₂
    exact alg_units (hu z J hJ) (hs' (E'.h y) b z J hJ) h₂ (fe_zero hGF D.tau_bimult s' y (hh y) b z J hJ) h₄
      (val_twist_zero hGF E.aB (map_zero E.h) (E.u 0) (E.u_norm 0) _ z J hJ)
      (by rw [cubN, Finset.prod_range_one, pow_zero, _root_.mul_one, C.face])
      (kappa_add hGF E.aB (hh y) hc κ hκ (E.u (E'.h y)) (E.u_norm _) b z J hJ)
  obtain ⟨z'⟩ := exists_pt (R := R) (F := F)
  obtain rfl : z = jFK (R := R) F z' := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  let ρ := jFK (R := R) F
  have : Surjective ρ := ⟨fun x => ⟨z', Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _⟩⟩
  have : Flat ρ := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))))
  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  obtain ⟨J', hJ', e⟩ := exists_good D.toPre.P.L D.toPre.P.isLB (Z := Spec (CommRingCat.of F)) z'
    (fun ψ : (TK R).left ⟶ D.toPre.P.A.left => ρ ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi ρ).1 e)) (fun ψ => hJ ψ)
  obtain rfl : (fun ψ => J' (ρ ≫ ψ)) = J := funext e
  have hinj : Function.Injective (ρ.stalkMap z').hom := by
    let _ := (ρ.stalkMap z').hom.toAlgebra
    have : Module.Flat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Flat.stalkMap ρ z'
    have : IsLocalHom (algebraMap ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z')) :=
      inferInstanceAs (IsLocalHom (ρ.stalkMap z').hom)
    have : Module.FaithfullyFlat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective ((TK R).left.presheaf.stalk (ρ z')) _
  have v₁ := fun χ => EvalZero.val_comp_map (D.toPre.psi χ) ρ (𝟙 _) ρ (Category.comp_id _) z' hJ'
  have v₂ := EvalZero.val_comp_map (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
    D.toPre.rig ρ (TK R).hom (TF (R := R) F).hom rfl z' hJ'
  have v₃ := EvalZero.val_comp_map κ ρ (D.toPre.xK y) (cP D.toPre (TF (R := R) F) y).left
    (Category.assoc _ _ _).symm z' hJ'
  refine Units.ext (hinj ?_)
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
    map_mul, map_pow, map_pow]
  have k := congrArg Units.val (key z' J' hJ')
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at k
  exact (congrArg₂ (· * ·) (v₁ _) v₂).symm.trans (k.trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (· ^ ν) (v₁ y)) v₃) (congrArg (· ^ ν) v₂)))

end GlobalTheory.UT.PsiPull
end
