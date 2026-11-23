import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.IntEnd

variable {R : Type} [CommRing R] [IsDomain R]

theorem cPoint_zsmul (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (χ : D.X) :
    cP D T (n • χ) = cP D T χ ^ n :=
  map_zpow (MonoidHom.mk' (fun x : Multiplicative D.X => cP D T x.toAdd) fun a b => cPoint_add D T a.toAdd b.toAdd)
    (Multiplicative.ofAdd χ) n

theorem prod_end (D : DegPre R) (n : ℤ) (χ : D.X) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (Sum.elim (D.Oφ (𝟙 _) (n • χ)) (D.Oφ (𝟙 D.P.A ^ n) χ) k) ^ Sum.elim Oε Oinvε k =
      h (cP D _ χ ^ n * 𝟙 D.P.A).left * (h (cP D _ χ ^ n).left)⁻¹ * (h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)⁻¹ *
        (h (cP D _ χ * 𝟙 D.P.A ^ n).left)⁻¹ * h (cP D _ χ).left * h (𝟙 D.P.A ^ n : D.P.A ⟶ D.P.A).left := by
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, ← cPoint_zsmul, mul_comm (cP D _ (n • χ)),
    mul_comm (cP D _ χ)]
  change h (𝟙 D.P.A * cP D _ (n • χ)).left ^ (1 : ℤ) * h (cP D _ (n • χ)).left ^ (-1 : ℤ) *
      h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * h (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
      (h (𝟙 D.P.A ^ n * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) *
      h (𝟙 D.P.A ^ n : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = _
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv]
  abel

def IsCmp (D : DegPre R) (n : ℤ) (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (n • χ)) (D.Oφ (𝟙 D.P.A ^ n) χ)) (Sum.elim Oε Oinvε))) : Prop :=
  u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    ∀ (a b : ℤ → (T.left.presheaf.stalk z)ˣ) (s : (T.left.presheaf.stalk z)ˣ), a 0 = 1 → b 0 = 1 →
      (∀ k, a (k + 1) * th D z J (cP D T χ ^ k) (cP D T χ) p = a k * s) →
      (∀ k, b (k + 1) * th D z J (cP D T χ) (p ^ k) p = b k * s) → b n = a n * val u p.left z J

theorem exists_step (D : DegPre R) (n : ℤ) (χ : D.X) :
    ∃ (K : Type) (_ : Fintype K) (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (v : LB.Gen (LB.LinComb D.P.L φ ε)),
      v.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U),
        (∏ k, h (Sum.elim (D.Oφ (𝟙 _) (n • χ)) (D.Oφ (𝟙 D.P.A ^ n) χ) k) ^ Sum.elim Oε Oinvε k) * ∏ k, h (φ k) ^ ε k =
        ∏ k, h (Sum.elim (D.Oφ (𝟙 _) ((n + 1) • χ)) (D.Oφ (𝟙 D.P.A ^ (n + 1)) χ) k) ^ Sum.elim Oε Oinvε k) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val v p.left z J = th D z J (cP D T χ ^ n) (cP D T χ) p * (th D z J (cP D T χ) (p ^ n) p)⁻¹ := by
  refine ⟨_, _, _, _, LB.mulGen D.P.L _ _ _ _
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D _ χ ^ n) (lift (cP D _ χ) (𝟙 D.P.A))).left)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D _ χ) (lift (𝟙 D.P.A ^ n) (𝟙 D.P.A))).left)),
    mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)), fun U _ h => ?_, fun T p z J hJ => ?_⟩
  · refine (congrArg₂ (· * ·) (prod_end D n χ h) (prod_sum₂ (K := thK) (K' := thK) (U := U) _
      (prod_cub (cP D _ χ ^ n) (cP D _ χ) (𝟙 D.P.A) h)
      (prod_neg _ _ (prod_cub (cP D _ χ) (𝟙 D.P.A ^ n) (𝟙 D.P.A) h)))).trans (Eq.trans ?_ (prod_end D (n + 1) χ h).symm)
    rw [zpow_add_one, zpow_add_one, _root_.mul_assoc (cP D _ χ) (𝟙 D.P.A ^ n)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub D.cub p hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub p hJ _ _ _))))).trans ?_
    rw [GrpObj.comp_zpow, GrpObj.comp_zpow, comp_cP, Category.comp_id]

theorem exists_isCmp (D : DegPre R) (n : ℤ) (χ : D.X) : ∃ u, IsCmp D n χ u := by
  induction n using Int.induction_on with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB
      (φ' := Sum.elim (D.Oφ (𝟙 _) ((0 : ℤ) • χ)) (D.Oφ (𝟙 D.P.A ^ (0 : ℤ)) χ)) (ε' := Sum.elim Oε Oinvε)
      (fun U _ h => by
        rw [prod_end, Fintype.prod_empty, zpow_zero, zpow_zero, _root_.one_mul, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel) (LB.oneGen D.P.L (Y := D.P.A.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T p z J hJ a b s a₀ b₀ _ _ => by rw [hv _ _ z J hJ, val_one, a₀, b₀, _root_.mul_one]⟩
  | succ n ih =>
    obtain ⟨u, hu, vu⟩ := ih
    obtain ⟨K, _, φ, ε, v, hv, fv, vv⟩ := exists_step D n χ
    obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB
      (φ' := Sum.elim (D.Oφ (𝟙 _) ((n + 1 : ℤ) • χ)) (D.Oφ (𝟙 D.P.A ^ (n + 1 : ℤ)) χ)) (ε' := Sum.elim Oε Oinvε)
      (fun U _ h => (Fintype.prod_sum_type _).trans (fv U h)) (LB.mulGen D.P.L _ _ _ _ u v)
      (mulGen_isGen _ _ _ _ _ _ _ hu hv)
    refine ⟨t, ht, fun T p z J hJ a b s a₀ b₀ ha hb => ?_⟩
    have e₁ := congrArg Additive.ofMul (vu T p z J hJ a b s a₀ b₀ ha hb)
    have e₂ := congrArg Additive.ofMul (ha n)
    have e₃ := congrArg Additive.ofMul (hb n)
    rw [vt _ _ z J hJ, val_mul hJ, vv T p z J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢
    linear_combination (norm := abel) e₁ - e₂ + e₃
  | pred n ih =>
    obtain ⟨K, _, φ, ε, v, hv, fv, vv⟩ := exists_step D (-n - 1) χ
    generalize hm : (-(n : ℤ) - 1) = m at *
    obtain e : -(n : ℤ) = m + 1 := by omega
    rw [e] at ih
    obtain ⟨u, hu, vu⟩ := ih
    obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB
      (φ' := Sum.elim (D.Oφ (𝟙 _) (m • χ)) (D.Oφ (𝟙 D.P.A ^ m) χ)) (ε' := Sum.elim Oε Oinvε)
      (fun U _ h => (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := K) (U := U) _ (fv U h).symm (prod_neg _ _ rfl)).trans
        (mul_inv_cancel_right _ _)) (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ v))
      (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ hv))
    refine ⟨t, ht, fun T p z J hJ a b s a₀ b₀ ha hb => ?_⟩
    have e₁ := congrArg Additive.ofMul (vu T p z J hJ a b s a₀ b₀ ha hb)
    have e₂ := congrArg Additive.ofMul (ha m)
    have e₃ := congrArg Additive.ofMul (hb m)
    rw [vt _ _ z J hJ, val_mul hJ, val_inv, vv T p z J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢
    linear_combination (norm := abel) e₁ + e₂ - e₃

theorem IsCmp.normd {D : DegPre R} {n : ℤ} {χ : D.X} {u} (hu : IsCmp D n χ u) : Normd u := by
  refine ⟨hu.1, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have C : IsCub (th D (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := hu.2 (𝟙_ _) 1 y J hJ (fun _ => 1) (fun _ => 1) 1 rfl rfl (fun k => by rw [C.face₃]) (fun k => by rw [C.face₃])
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = η[D.P.A] := by simp [Hom.one_def]
  rw [_root_.one_mul, o] at e
  rw [val_pull hJ, val_one, Category.id_comp]
  exact e.symm

theorem map_id_zpow {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (n : ℤ) :
    (Over.pullback f).map (𝟙 H ^ n) = 𝟙 ((Over.pullback f).obj H) ^ n :=
  (map_zpow ((Over.pullback f).homMonoidHom (X := H) (M := H)) (𝟙 H) n).trans
    (congrArg (· ^ n) ((Over.pullback f).map_id H))

theorem id_zpow_comm {S : Scheme.{0}} {H H' : Over S} [GrpObj H] [GrpObj H'] (q : H ⟶ H') [IsMonHom q] (n : ℤ) :
    (𝟙 H ^ n) ≫ q = q ≫ 𝟙 H' ^ n := by
  rw [GrpObj.zpow_comp, GrpObj.comp_zpow, Category.id_comp, Category.comp_id]

theorem torusEndOf_zpow (S : Scheme.{0}) (X : Type) [AddCommGroup X] (n : ℤ) :
    TorusEndOf X (fun χ => n • χ) (𝟙 (splitTorus S X) ^ n) := by
  intro χ
  apply Units.ext
  have key : ∀ (t : splitTorus S X ⟶ splitTorus S X) (h : (⊤ : (splitTorus S X).left.Opens) ≤ t.left ⁻¹ᵁ ⊤),
      (res h (pullU t.left ⊤ (charUnit S X χ))).val = t.left.appTop.hom (charUnit S X χ).val := fun t h => by
    have : (res h (pullU t.left ⊤ (charUnit S X χ))).val = (t.left.appLE ⊤ ⊤ h).hom (charUnit S X χ).val := rfl
    rw [this]
    exact congrArg (fun φ => φ.hom (charUnit S X χ).val) (Scheme.Hom.appLE_eq_app t.left (U := ⊤))
  refine (key _ _).trans ?_
  rw [← splitTorusPointsEquiv_val, map_zpow, MonoidHom.zpow_apply, ← map_zpow, ← ofAdd_zsmul,
    splitTorusPointsEquiv_val]
  simp

section Coord

open GlobalTheory.TorusCoord

variable {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (g : GtCoord I D e G)

theorem im_zpow {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) (k : ℤ) :
    im g (x ^ k) = im g x ^ k :=
  map_zpow (MonoidHom.mk' (fun y : T ⟶ thickObj R I e G => im g y) (im_mul g)) x k

theorem val_t_add {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) (χ χ' : D.X)
    {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (g.t (χ + χ')) x.left z J * @id (T.left.presheaf.stalk z)ˣ (th D (T := (Over.map (thick R I e)).obj T) z J
      (cP D _ χ) (cP D _ χ') (im g x)) = val (g.t χ) x.left z J * val (g.t χ') x.left z J := by
  have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul χ χ') x.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg (_ * ·) ?_) h
  refine Eq.trans ?_ (val_cub D.cub ((Over.map (thick R I e)).map x) hJ _ _ _).symm
  rw [← comp_cP D ((Over.map (thick R I e)).map x) χ, ← comp_cP D ((Over.map (thick R I e)).map x) χ']
  rfl

theorem val_t_zpow (hG : GlobalFnsSt) {n : ℤ} {χ : D.X} {u} (hu : IsCmp D n χ u)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    val (g.t χ) (x ^ n).left z J = val (g.t (n • χ)) x.left z J * val u (x.left ≫ g.pG.left) z J := by
  have C : IsCub (th D (T := (Over.map (thick R I e)).obj T) z J) := isCub_cubV D.cub hJ
  refine hu.2 ((Over.map (thick R I e)).obj T) (im g x) z J hJ (fun k => val (g.t (k • χ)) x.left z J)
    (fun k => val (g.t χ) (x ^ k).left z J) (val (g.t χ) x.left z J) ?_ ?_ (fun k => ?_) (fun k => ?_)
  · have h := val_t_add g x 0 0 hJ
    rw [add_zero, cPoint_zero, id, C.face] at h
    have h' : val (g.t 0) x.left z J = 1 := left_eq_mul.1 ((_root_.mul_one _).symm.trans h)
    exact (congrArg (fun w => val (g.t w) x.left z J) (zero_zsmul χ)).trans h'
  · exact (val_congr g χ (zpow_zero x) z J).trans (val_unit g χ hJ)
  · have h := val_t_add g x (k • χ) χ hJ
    rw [cPoint_zsmul, ← add_one_zsmul] at h
    exact h
  · have h := val_t_mul_points g hG χ (x ^ k) x z J hJ
    rw [← zpow_add_one, cubeVal, im_zpow] at h
    exact h

end Coord

section Points

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem zsmul_b (n : ℤ) (g : GtPtF D F) : (n • g).b = g.b ^ n :=
  congrArg Additive.toMul (map_zsmul (gtProj D F) n g)

theorem charVal_zsmul {n : ℤ} {χ : D.X} {u} (hu : IsCmp D n χ u) (g : GtPtF D F) {y J} (hJ : Good D.P.L y J) :
    charVal (n • g) χ y J = charVal g (n • χ) y J * val u g.b.left y J := by
  refine hu.2 _ g.b y J hJ (fun k => charVal g (k • χ) y J) (fun k => charVal (k • g) χ y J) (charVal g χ y J)
    ?_ ?_ (fun k => ?_) (fun k => ?_)
  · exact (congrArg (fun w => charVal g w y J) (zero_zsmul χ)).trans (charVal_zero g hJ)
  · exact (congrArg (fun w => charVal w χ y J) (zero_zsmul g)).trans (zero_val χ hJ)
  · have h := charVal_add g hJ (k • χ) χ
    rw [cPoint_zsmul, ← add_one_zsmul] at h
    exact h
  · have h := add_val (k • g) g χ hJ
    rw [zsmul_b, ← add_one_zsmul] at h
    exact h

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def intEnd (hG : GlobalFnsSt) (U : UnifPre I D A G) (n : ℤ) : EndU U where
  aG := 𝟙 G ^ n
  aA := 𝟙 A.A ^ n
  aB := 𝟙 D.toPre.P.A ^ n
  homG := GlobalTheory.Serre.isMonHom_zpow _ n
  homA := GlobalTheory.Serre.isMonHom_zpow _ n
  homB := GlobalTheory.Serre.isMonHom_zpow _ n
  h := AddMonoidHom.mk' (fun χ => n • χ) (zsmul_add · · n)
  ext := by
    have := U.gen_hom
    rw [map_id_zpow, id_zpow_comm]
  q_lin e := by
    have := (U.gt e).q_hom
    rw [map_id_zpow, map_id_zpow, id_zpow_comm]
  i_lin e := ⟨_, torusEndOf_zpow _ _ n, by
    have := (U.gt e).i_hom
    rw [map_id_zpow, id_zpow_comm]⟩
  u χ := (exists_isCmp D.toPre n χ).choose
  u_norm χ := (exists_isCmp D.toPre n χ).choose_spec.normd
  t_lin e χ Z x z J hJ := by
    let x' : Over.mk (x ≫ (thickObj R I e G).hom) ⟶ thickObj R I e G := Over.homMk x rfl
    have h := val_t_zpow (U.gt e) hG (exists_isCmp D.toPre n χ).choose_spec x' hJ
    have e' : x' ^ n = x' ≫ (Over.pullback (thick R I e)).map (𝟙 G ^ n) := by
      rw [map_id_zpow, GrpObj.comp_zpow, Category.comp_id]
    rw [e'] at h
    exact h

theorem intEnd_act (hG : GlobalFnsSt) (U : UnifPre I D A G) (n : ℤ) (g g' : GtPtF D.toPre F) :
    (intEnd hG U n).Act g g' ↔ g' = n • g := by
  have b : (n • g).b = g.b ≫ 𝟙 D.toPre.P.A ^ n := by rw [zsmul_b, GrpObj.comp_zpow, Category.comp_id]
  constructor
  · rintro ⟨hb, hv⟩
    exact gt_ext_val (hb.trans b.symm) fun χ y J hJ =>
      (hv χ y J hJ).trans (charVal_zsmul (exists_isCmp D.toPre n χ).choose_spec g hJ).symm
  · rintro rfl
    exact ⟨b, fun χ y J hJ => charVal_zsmul (exists_isCmp D.toPre n χ).choose_spec g hJ⟩

theorem exists_nsmul_and_neg : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => (∀ m : ℕ, ∃ E : EndU U.toUnifPre, E.aG = 𝟙 G ^ m ∧ E.aA = 𝟙 A.A ^ m ∧ E.aB = 𝟙 D.toPre.P.A ^ m ∧ (∀ χ, E.h χ = m • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtPtF.IsNsmul m g g') ∧ ∃ E : EndU U.toUnifPre, E.aG = (𝟙 G)⁻¹ ∧ E.aA = (𝟙 A.A)⁻¹ ∧ E.aB = (𝟙 D.toPre.P.A)⁻¹ ∧ (∀ χ, E.h χ = -χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ ∃ z : GtPtF D.toPre F, z.IsZero ∧ g.IsAdd g' z := by
  intro hL R _ _ _ I _ D A G _ _ _ U
  refine ⟨fun m => ⟨intEnd hL.1.globalFns U.toUnifPre m, zpow_natCast _ _, zpow_natCast _ _, zpow_natCast _ _,
    fun χ => natCast_zsmul χ m, fun F _ _ g g' => ?_⟩, intEnd hL.1.globalFns U.toUnifPre (-1), zpow_neg_one _,
    zpow_neg_one _, zpow_neg_one _, fun χ => neg_one_zsmul χ, fun F _ _ g g' => ?_⟩
  · rw [intEnd_act, isNsmul_iff_eq, natCast_zsmul]
  · rw [intEnd_act, neg_one_zsmul]
    constructor
    · rintro rfl
      exact ⟨0, (isZero_iff_eq _).2 rfl, (isAdd_iff_eq _ _ _).2 (add_neg_cancel g).symm⟩
    · rintro ⟨z, hz, ha⟩
      exact eq_neg_of_add_eq_zero_right (((isAdd_iff_eq _ _ _).1 ha).symm.trans ((isZero_iff_eq _).1 hz))

end Points

end GlobalTheory.IntEnd
