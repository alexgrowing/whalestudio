import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

def matAddEquiv {M : Type*} [AddCommGroup M] (S : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) :
    (Fin 8 → M) ≃+ (Fin 8 → M) where
  toFun w v := ∑ u, S v u • w u
  invFun w v := ∑ u, S.adjugate v u • w u
  left_inv w := by
    funext v
    have h : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv w := by
    funext v
    have h : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

def sumChars {X X' : Type*} [AddCommGroup X] [AddCommGroup X'] (c : Fin 8 → (X →+ X')) : (Fin 8 → X) →+ X' where
  toFun y := ∑ v, c v (y v)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem e8data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have hpG : ∀ v, ∃ F : G' ⟶ G, IsMonHom F ∧
      (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := by
    intro v
    haveI := hpr v
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose pG hpGm hpGg using hpG
  have hgen : ∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    rw [hpGg v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose c hc using fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hR G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  have hbij := (characters_eighthPower_elementaryMatrices R hR hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hgen c hc).1
  let Φ := AddEquiv.ofBijective (sumChars c) hbij
  let Sm := matAddEquiv (M := D.toPre.X) (W + W.transpose) hW.2
  refine ⟨pG, c, Φ.symm.trans Sm.symm, hpGm, hgen, hc, fun y => ?_⟩
  have h1 : Sm ((Φ.symm.trans Sm.symm) y) = Φ.symm y := by simp
  have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [← h1] at h2
  exact h2

end GlobalTheory.Poinc.Eq8
