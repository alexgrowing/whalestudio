import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProdStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensMono

def tensForm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ) (xe : Y ≃+ (Fin r → X))
    (b : LinearMap.BilinForm ℤ X) : LinearMap.BilinForm ℤ Y :=
  ∑ i, ∑ j, S i j • b.compl₁₂ ((LinearMap.proj i).comp xe.toIntLinearEquiv.toLinearMap)
    ((LinearMap.proj j).comp xe.toIntLinearEquiv.toLinearMap)

theorem tensForm_apply {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (y z : Y) :
    tensForm S xe b y z = ∑ i, ∑ j, S i j * b (xe y i) (xe z j) := by
  simp [tensForm, LinearMap.sum_apply]

theorem zpow_sum_local {G κ : Type} [CommGroup G] (a : G) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensForm_self {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y : Y) :
    tensForm (W + W.transpose) xe b y y = 2 * ∑ i, ∑ j, W i j * b (xe y i) (xe y j) := by
  rw [tensForm_apply]
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib]
  rw [two_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb]

theorem tensForm_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y z : Y) :
    tensForm (W + W.transpose) xe b y z = tensForm (W + W.transpose) xe b z y := by
  rw [tensForm_apply, tensForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]; simp only [Matrix.add_apply, Matrix.transpose_apply]; ring

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  intro R _ _ _ Q D' r W pr xe hW hT m t β hmono ht hsym hnn hdef
  have hreal : ∀ l y, ((tensForm (W + W.transpose) xe (β l) y y : ℤ) : ℝ) =
      ∑ i, ∑ j, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) i j *
        (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) i j := by
    intro l y; rw [tensForm_apply]; push_cast; simp [Matrix.map_apply]
  have hpos : ∀ l y, 0 ≤ tensForm (W + W.transpose) xe (β l) y y := fun l y => by
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).1
    rw [← hreal] at this; exact_mod_cast this
  refine ⟨fun l => tensForm (W + W.transpose) xe (β l), ?_, fun l y z => tensForm_symm W xe (β l) (hsym l) y z, ?_⟩
  · intro y
    have hn : ∀ l, (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) = ((∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat : ℤ) :=
      fun l => (Int.toNat_of_nonneg (by have := hpos l y; rw [tensForm_self W xe (β l) (hsym l)] at this; omega)).symm
    choose k hk hkc using fun i j => hmono (xe y i) (xe y j)
    obtain ⟨x, hx⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D' y
    obtain ⟨u, hu⟩ := GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod R Q D' W pr xe hT y k hkc x hx
    have ht' : ∀ l, algebraMap R (FractionRing R) (t l) ≠ 0 := fun l =>
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht l)
    let a : Fin m → (FractionRing R)ˣ := fun l => Units.mk0 _ (ht' l)
    have hk' : ∀ i j, k i j = ∏ l, a l ^ β l (xe y i) (xe y j) := fun i j => Units.ext (by
      rw [hk, Units.coe_prod]
      exact Finset.prod_congr rfl fun l _ => by rw [Units.val_zpow_eq_zpow_val]; rfl)
    have hprod : ∏ i, ∏ j, k i j ^ W i j = ∏ l, a l ^ (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) := by
      calc ∏ i, ∏ j, k i j ^ W i j = ∏ i, ∏ j, ∏ l, a l ^ (β l (xe y i) (xe y j) * W i j) := by
            refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
            rw [hk', ← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun l _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ l, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) :=
            Finset.prod_congr rfl fun i _ => Finset.prod_comm
        _ = ∏ l, ∏ i, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) := Finset.prod_comm
        _ = _ := Finset.prod_congr rfl fun l _ => by
            rw [zpow_sum_local]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [zpow_sum_local]
            exact Finset.prod_congr rfl fun j _ => by rw [mul_comm]
    refine ⟨u, fun l => (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat, fun l => by
      rw [tensForm_self W xe (β l) (hsym l), hn l], (GlobalTheory.PeriodFormCompare.psiCoord_iff D' y _).2 ⟨x, hx, ?_⟩⟩
    rw [hu, hprod]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_prod, map_mul, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hn l, zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  · intro y hy
    obtain ⟨j, hj⟩ : ∃ j, xe y j ≠ 0 := by
      by_contra h; push_neg at h
      exact hy (xe.injective (by rw [map_zero]; exact funext h))
    obtain ⟨l, hl⟩ := hdef _ hj
    refine ⟨l, ?_⟩
    have hG : (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) ≠ 0 := fun h => by
      have := congrFun (congrFun h j) j
      simp at this; omega
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).2 hG
    rw [← hreal] at this; exact_mod_cast this

end GlobalTheory.TensMono
