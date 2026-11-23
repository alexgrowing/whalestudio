import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPow

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowTorusCoord

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoordPull GlobalTheory.PowLevelCompat GlobalTheory.SplitTorusPow

section Char

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem gm_char {T : Over S} (r : T ⟶ splitTorus S X) (y : T.left) (χ : X) :
    gm r.left y ⊤ (charUnit S X χ) =
      gm (𝟙 T.left) y ⊤ (splitTorusPointsEquiv S X T r (Multiplicative.ofAdd χ)) := by
  refine Eq.trans ?_ ((gm_pull (𝟙 T.left) r.left y ⊤ trivial (charUnit S X χ)).symm.trans
    (congrArg (gm (𝟙 T.left) y ⊤) (Units.ext (splitTorusPointsEquiv_val S X T r χ).symm)))
  rw [Category.id_comp]

theorem gm_char_pow {j : ℕ} (xe : X' ≃+ (Fin j → X)) {T : Over S} (r : T ⟶ splitTorus S X') (y : T.left) (x : X') :
    gm r.left y ⊤ (charUnit S X' x) =
      ∏ i, gm (r ≫ torusMap S (incl xe i)).left y ⊤ (charUnit S X (xe x i)) := by
  have e : Multiplicative.ofAdd x = ∏ i, Multiplicative.ofAdd (incl xe i (xe x i)) := by
    rw [← ofAdd_sum, sum_incl]
  rw [gm_char, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gm_char, points_comp_torusMap]
  rfl

end Char

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem cPoint_proj (T : Over (Spec (CommRingCat.of R))) (χ : D'.X) (i : Fin j) :
    cP D' T χ ≫ pD.pw.pr i = cP D T (pD.xe χ i) := by
  rw [cP, cP, Category.assoc, pD.c_pr]

variable {T T' : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (ρ : Fin j → (T' ⟶ T))
  (hp : ∀ i, p' ≫ pD.pw.pr i = ρ i ≫ p)

include hp in
theorem Oφ_proj (x : D'.X) (i : Fin j) (κ : Fin 4) :
    D'.Oφ p' x κ ≫ (pD.pw.pr i).left = (ρ i).left ≫ D.Oφ p (pD.xe x i) κ := by
  haveI := pD.pw.hom i
  refine Eq.trans ?_ (WeightPf.Oφ_comp (ρ i) p (pD.xe x i) κ).symm
  rw [← hp]
  fin_cases κ
  · refine congrArg (fun q : T' ⟶ D.P.A => q.left)
      (?_ : (p' * cP D' _ x) ≫ pD.pw.pr i = (p' ≫ pD.pw.pr i) * cP D _ (pD.xe x i))
    rw [MonObj.mul_comp, cPoint_proj]
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (cPoint_proj pD _ x i)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.one_comp (pD.pw.pr i))

def omg {Z : Scheme.{0}} (y : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι)
    (ψ : Z ⟶ D'.P.A.left) : (Z.presheaf.stalk y)ˣ :=
  bw pD.w ψ y (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ)

def BoxMaps (x : D'.X) (a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε))
    (t : ∀ i, LB.Gen (LB.LinComb D.P.L (D.Oφ p (pD.xe x i)) Oinvε)) : Prop :=
  LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) a (GeneratorPullback.boxGen D.P.L (fun i => (pD.pw.pr i).left) _ Oinvε
    (fun i => GeneratorPullback.pullAlong D.P.L (pD.pw.pr i).left (ρ i).left _ Oinvε _ (Oφ_proj pD p p' ρ hp x i) (t i)))

theorem val_box {x : D'.X} {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε)}
    {t : ∀ i, LB.Gen (LB.LinComb D.P.L (D.Oφ p (pD.xe x i)) Oinvε)} (H : BoxMaps pD p p' ρ hp x a t)
    {T₀ : Over (Spec (CommRingCat.of R))} (r : T₀ ⟶ T') {y : T₀.left} {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    (omg pD y J J' ((r ≫ p') * cP D' T₀ x).left)⁻¹ * omg pD y J J' (cP D' T₀ x).left * omg pD y J J' (r ≫ p').left *
      (omg pD y J J' (1 : T₀ ⟶ D'.P.A).left)⁻¹ * val a r.left y J' = ∏ i, val (t i) (r.left ≫ (ρ i).left) y J := by
  refine Eq.trans ?_ (box_gen_val_along pD.w (Oφ_proj pD p p' ρ hp x) a t H r.left y hJ hJ')
  rw [← prod_O D' (r ≫ p') x (omg pD y J J')]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) rfl
  rw [← WeightPf.Oφ_comp]
  rfl

theorem mul_box (hG : GlobalFnsSt) (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ p χ) Oinvε))
    (a : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε))
    (H : ∀ x, BoxMaps pD p p' ρ hp x (a x) (fun i => t (pD.xe x i)))
    (hm : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') p)).left))
      (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) (χ χ' : D'.X) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.mulGen D'.P.L _ _ _ _ (a (χ + χ'))
        (LB.pullGen D'.P.L (thφ D'.P.A (x3 D'.P.A)) thε D'.cub.t
          (lift (toUnit _ ≫ D'.c χ) (lift (toUnit _ ≫ D'.c χ') p')).left))
      (LB.mulGen D'.P.L _ _ _ _ (a χ) (a χ')) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have va : ∀ x, (omg pD y J J' (p' * cP D' T' x).left)⁻¹ * omg pD y J J' (cP D' T' x).left *
      omg pD y J J' p'.left * (omg pD y J J' (1 : T' ⟶ D'.P.A).left)⁻¹ * val (a x) (𝟙 T'.left) y J' =
      ∏ i, val (t (pD.xe x i)) (ρ i).left y J := fun x => by
    have := val_box pD p p' ρ hp (H x) (𝟙 T') hJ hJ'
    simpa only [Category.id_comp, Over.id_left] using this
  have c : cubV D'.cub y J' (cP D' T' χ) (cP D' T' χ') p' *
      (omg pD y J J' (cP D' T' χ * cP D' T' χ' * p').left * (omg pD y J J' (cP D' T' χ * cP D' T' χ').left)⁻¹ *
        (omg pD y J J' (cP D' T' χ * p').left)⁻¹ * (omg pD y J J' (cP D' T' χ' * p').left)⁻¹ *
        omg pD y J J' (cP D' T' χ).left * omg pD y J J' (cP D' T' χ').left * omg pD y J J' p'.left *
        (omg pD y J J' (1 : T' ⟶ D'.P.A).left)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD T' y J J' hJ hJ' (cP D' T' χ) (cP D' T' χ') p'
  have m : ∀ i, val (t (pD.xe (χ + χ') i)) (ρ i).left y J *
      cubV D.cub y J (cP D' T' χ ≫ pD.pw.pr i) (cP D' T' χ' ≫ pD.pw.pr i) (p' ≫ pD.pw.pr i) =
      val (t (pD.xe χ i)) (ρ i).left y J * val (t (pD.xe χ' i)) (ρ i).left y J := fun i => by
    have vc := val_cub D.cub (ρ i) hJ (cP D T (pD.xe χ i)) (cP D T (pD.xe χ' i)) p
    rw [comp_cP, comp_cP] at vc
    rw [cPoint_proj, cPoint_proj, hp, map_add, Pi.add_apply]
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl vc)).symm.trans
      ((val_corr hJ (hm (pD.xe χ i) (pD.xe χ' i)) (ρ i).left).trans (val_mul hJ _ _ _))
  have m' := Finset.prod_congr (s₁ := Finset.univ) rfl fun i _ => m i
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← c, ← va, ← va, ← va, cPoint_add, mul_comm p', mul_comm p',
    mul_comm p'] at m'
  have vc := val_cub D'.cub (𝟙 T') hJ' (cP D' T' χ) (cP D' T' χ') p'
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at vc
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl vc)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  show val (a (χ + χ')) (𝟙 T'.left) y J' * cubV D'.cub y J' (cP D' T' χ) (cP D' T' χ') p' =
    val (a χ) (𝟙 T'.left) y J' * val (a χ') (𝟙 T'.left) y J'
  apply Additive.ofMul.injective
  have m'' := congrArg Additive.ofMul m'
  simp only [ofMul_mul, ofMul_inv] at m'' ⊢
  linear_combination (norm := abel) m''

end Pow

section Clauses

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)
  {S : Scheme.{0}} {s : S ⟶ Spec (CommRingCat.of R)} {G G' : Over S} [GrpObj G] [GrpObj G']
  (p : (Over.map s).obj G ⟶ D.P.A) (p' : (Over.map s).obj G' ⟶ D'.P.A) (σ : Fin j → (G' ⟶ G))
  (hσ : ∀ i, IsMonHom (σ i)) (hp : ∀ i, p' ≫ pD.pw.pr i = (Over.map s).map (σ i) ≫ p) {χ : D'.X}
  {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε)}
  {t : ∀ i, LB.Gen (LB.LinComb D.P.L (D.Oφ p (pD.xe χ i)) Oinvε)}
  (H : BoxMaps pD p p' (fun i => (Over.map s).map (σ i)) hp χ a t)

include hσ H in
theorem unit_box (e₂ : (Over.map s).map η[G'] ≫ p' = 1)
    (hu : ∀ i, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t i) (eSec G)) (LB.oneGen D.P.L)) :
    LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (eSec G')) (LB.oneGen D'.P.L) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have e₃ := val_box pD p p' _ hp H ((Over.map s).map η[G']) (y := y) hJ hJ'
  rw [e₂, _root_.one_mul, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e₃
  have e₅ : val a (eSec G') y J' = 1 := e₃.trans (Finset.prod_eq_one fun i _ => by
    have := hσ i
    have e₁ : eSec G' ≫ (σ i).left = 𝟙 S ≫ eSec G :=
      (congrArg (fun q => q.left) (IsMonHom.one_hom (σ i))).trans (Category.id_comp _).symm
    exact (congrArg (fun r => val (t i) r y J) e₁).trans
      ((val_pull hJ _ _ _).symm.trans ((val_corr hJ (hu i) (𝟙 S)).trans (val_one _))))
  exact (val_pull hJ' _ _ _).trans ((congrArg (fun r => val a r y J') (Category.id_comp _)).trans
    (e₅.trans (val_one _).symm))

include hσ H in
theorem weight_box (κ : splitTorus S D.X ⟶ G) (κ' : splitTorus S D'.X ⟶ G')
    (hκ : ∀ i, κ' ≫ σ i = torusMap S (incl pD.xe i) ≫ κ)
    (aO : (Over.map s).map (lift (fst (splitTorus S D'.X) G' ≫ κ') (snd _ _) ≫ μ[G']) ≫ p' =
      (Over.map s).map (snd (splitTorus S D'.X) G') ≫ p')
    (hw : ∀ i, LB.Gen.Corr D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (t i) (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left)
      (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L (pD.xe χ i))
        (LB.pullGen D.P.L _ _ (t i) (snd (splitTorus S D.X) G).left))) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.pullGen D'.P.L _ _ a (lift (fst (splitTorus S D'.X) G' ≫ κ') (snd _ _) ≫ μ[G']).left)
      (LB.mulGen D'.P.L _ _ _ _ (charGen D'.X G' D'.P.L χ)
        (LB.pullGen D'.P.L _ _ a (snd (splitTorus S D'.X) G').left)) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have v₃ : ∀ i, val (t i) ((lift (fst (splitTorus S D'.X) G' ≫ κ') (snd _ _) ≫ μ[G']) ≫ σ i).left y J =
      gm (fst (splitTorus S D'.X) G' ≫ torusMap S (incl pD.xe i)).left y ⊤ (charUnit _ D.X (pD.xe χ i)) *
        val (t i) (snd (splitTorus S D'.X) G' ≫ σ i).left y J := fun i => by
    have := hσ i
    let N : splitTorus S D'.X ⊗ G' ⟶ splitTorus S D.X ⊗ G := torusMap S (incl pD.xe i) ⊗ₘ σ i
    have n₁ : N ≫ fst _ _ = fst _ _ ≫ torusMap S (incl pD.xe i) := tensorHom_fst _ _
    have n₂ : N ≫ snd _ _ = snd _ _ ≫ σ i := tensorHom_snd _ _
    have n₃ : N ≫ (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]) =
        (lift (fst (splitTorus S D'.X) G' ≫ κ') (snd _ _) ≫ μ[G']) ≫ σ i := by
      rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, n₁, n₂, Category.assoc,
        Category.assoc, hκ]
    rw [← n₁, ← n₂, ← n₃]
    exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hw i) N.left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))
  have b₁ := val_box pD p p' _ hp H ((Over.map s).map (lift (fst (splitTorus S D'.X) G' ≫ κ') (snd _ _) ≫ μ[G']))
    (y := y) hJ hJ'
  have b₂ := val_box pD p p' _ hp H ((Over.map s).map (snd (splitTorus S D'.X) G')) (y := y) hJ hJ'
  rw [aO] at b₁
  have v₄ := b₁.trans ((Finset.prod_congr rfl fun i _ => v₃ i).trans (Finset.prod_mul_distrib.trans
    ((congrArg₂ (fun u v : (((Over.map s).obj (splitTorus S D'.X ⊗ G')).left.presheaf.stalk y)ˣ => u * v)
      (gm_char_pow pD.xe _ y χ).symm b₂.symm).trans (mul_left_comm _ _ _))))
  have v₅ := mul_left_cancel v₄
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_mul hJ' _ _ _).trans
    (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ' _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end Clauses

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G), ∃ g' : GtCoord I D'.toPre e G', (∀ (i : Fin j), g'.q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ g.q) ∧ (∀ (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map g'.q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map g.q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) (g'.t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) (g.t (pD.xe x i))))) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD _ pG e g
  obtain ⟨pGe, hGe⟩ := isPowGrp_baseChange _ _ (thick R I e) G' G j pG
  obtain ⟨pBe, hBe⟩ := isPowGrp_baseChange _ _ (thick R I e) D'.toPre.P.A D.toPre.P.A j pD.pw
  obtain ⟨q', hq, q_hom, q_flat, q_surj, -, q_aff⟩ := PowMap.main _ _ _ _ _ j pGe pBe g.q
  obtain ⟨i', hi, i_hom, -⟩ := PowMap.main _ _ _ _ _ j (isPowGrp _ pD.xe) pGe g.i
  have hker := PowKernel.main _ _ _ _ _ _ _ j (isPowGrp _ pD.xe) pGe pBe g.i g.q i' q' hi hq g.isKernel
  replace q_hom := q_hom g.q_hom
  simp only [hGe, hBe] at hq hi
  have hσ : ∀ i, IsMonHom ((Over.pullback (thick R I e)).map (pG.pr i)) := fun i => hGe i ▸ pGe.hom i
  have hp : ∀ i, ((Over.map (thick R I e)).map q' ≫ D'.toPre.prBe I e) ≫ pD.pw.pr i =
      (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map (pG.pr i)) ≫ g.pG := fun i => by
    have b : D'.toPre.prBe I e ≫ pD.pw.pr i =
        (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map (pD.pw.pr i)) ≫ D.toPre.prBe I e :=
      Over.OverMorphism.ext (pullback.lift_fst _ _ _).symm
    rw [Category.assoc, b, ← Category.assoc, ← Functor.map_comp, hq, Functor.map_comp, Category.assoc]
  have hO := Oφ_proj pD g.pG ((Over.map (thick R I e)).map q' ≫ D'.toPre.prBe I e) _ hp
  choose a ha H using fun x : D'.toPre.X => BoxQk.exists_box_maps pD.w pD.w_gen D.toPre.P.isLB D'.toPre.P.isLB _ (hO x)
    (fun i => g.t (pD.xe x i)) (fun i => g.t_gen _)
  have e₂ : (Over.map (thick R I e)).map η[thickObj R I e G'] ≫
      ((Over.map (thick R I e)).map q' ≫ D'.toPre.prBe I e) = 1 := by
    rw [← Category.assoc, ← Functor.map_comp, IsMonHom.one_hom]
    refine Over.OverMorphism.ext ((cubeMapOf (isGrpPullback_pullback D'.toPre.P.A (thick R I e))).e_comm.trans ?_)
    show thick R I e ≫ η[D'.toPre.P.A].left = (𝟙 _ ≫ thick R I e) ≫ η[D'.toPre.P.A].left
    rw [Category.id_comp]
  have aq : ((fst (splitTorus _ D'.toPre.X) (thickObj R I e G') ≫ i') * snd _ _) ≫ q' = snd _ _ ≫ q' := by
    rw [MonObj.mul_comp, Category.assoc, hker.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have aO : (Over.map (thick R I e)).map (lift (fst (splitTorus _ D'.toPre.X) (thickObj R I e G') ≫ i') (snd _ _) ≫
        μ[thickObj R I e G']) ≫ ((Over.map (thick R I e)).map q' ≫ D'.toPre.prBe I e) =
      (Over.map (thick R I e)).map (snd (splitTorus _ D'.toPre.X) (thickObj R I e G')) ≫
        ((Over.map (thick R I e)).map q' ≫ D'.toPre.prBe I e) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Hom.mul_def, aq, Functor.map_comp, Category.assoc]
  exact ⟨⟨q', q_hom, q_flat g.q_flat, q_surj g.q_surj, q_aff g.q_affine, i', i_hom g.i_hom, hker, a, ha,
    mul_box pD g.pG _ _ hp hG g.t a H g.t_mul,
    fun χ => unit_box pD g.pG _ _ hσ hp (H χ) e₂ (fun i => g.t_unit _),
    fun χ => weight_box pD g.pG _ _ hσ hp (H χ) g.i i' hi aO (fun i => g.t_weight _)⟩,
    hq, fun x => ⟨hO x, H x⟩⟩

end GlobalTheory.PowTorusCoord
