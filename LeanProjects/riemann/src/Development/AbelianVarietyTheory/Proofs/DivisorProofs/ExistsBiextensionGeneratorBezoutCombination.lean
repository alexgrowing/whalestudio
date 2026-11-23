import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriodsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LamComb

section Generators

variable {X Y Z : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]

omit [Fintype J] in
theorem wchart_le (φ : J → K → (Y ⟶ X)) [Fintype J] (jj : J × K → L.ι) (i : J) :
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj ≤ LB.wchart L (φ i) (fun k => jj (i, k)) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)

def prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (fun q : J × K => φ q.1 q.2) (fun q => δ q.1 * ε q.1 q.2)) where
  s := fun jj => ∏ i, res (wchart_le φ jj i) ((t i).s (fun k => jj (i, k))) ^ δ i

theorem gm_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) (z : Z) (jj : J × K → L.ι) (h : r z ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj) :
    gm r z (LB.wchart L (fun q : J × K => φ q.1 q.2) jj) ((prodGen φ ε δ t).s jj) =
      ∏ i, gm r z (LB.wchart L (φ i) (fun k => jj (i, k))) ((t i).s (fun k => jj (i, k))) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem isGen_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (ht : ∀ i, (t i).IsGen) : (prodGen φ ε δ t).IsGen := by
  intro jj jj'
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj ⊓
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj' := hy
  refine (gm_res (𝟙 Y) y _ hm _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y jj jj' hm.1 hm.2) (gm_res (𝟙 Y) y _ hm _))).symm)
  refine (gm_prodGen φ ε δ t (𝟙 Y) y jj hm.1).trans
    (Eq.trans ?_ (congrArg _ (gm_prodGen φ ε δ t (𝟙 Y) y jj' hm.2)).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gen_trans (ht i) (𝟙 Y) y (wchart_le φ jj i hm.1) (wchart_le φ jj' i hm.2), mul_zpow]
  congr 1
  rw [trF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem val_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X) → L.ι} (hI : Good L z I) :
    val (prodGen φ ε δ t) r z I = ∏ i, val (t i) r z I ^ δ i :=
  gm_prodGen φ ε δ t r z _ (hI.mem _ r)

end Generators

theorem prod_zpow_sum {U J : Type} [CommGroup U] (s : Finset J) (a : U) (f : J → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_lam_comb : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  intro R _ _ D hD r e c hec
  choose g hg hv using fun j => GlobalTheory.T.exists_lambdaGenerator_zpow_with_periods D hD (c j)
  have hF : FormEq (fun q : Fin r × (Fin 4 ⊕ Fin 4) => Sum.elim
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)) q.2)
      (fun q => e q.1 * Sum.elim Oε (fun l => -c q.1 * Oε l) q.2)
      (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
      (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) := by
    intro U _ h
    simp only [Fintype.prod_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    have k : ∀ l, ∏ j, h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (e j * (-c j * Oε l)) =
        h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (-Oε l) := fun l => by
      rw [prod_zpow_sum]
      congr 1
      calc ∑ j, e j * (-c j * Oε l) = (∑ j, e j * c j) * (-Oε l) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = -Oε l := by rw [hec, _root_.one_mul]
    simp only [k]
    rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Fin.prod_univ_four]
    have q0 : psum D.P.A (x2 D.P.A) ∅ = 1 := rfl
    have q1 : psum D.P.A (x2 D.P.A) {0} = fst D.P.A D.P.A := _root_.mul_one _
    have q2 : psum D.P.A (x2 D.P.A) {1} = snd D.P.A D.P.A := _root_.mul_one _
    have q3 : psum D.P.A (x2 D.P.A) {0, 1} = fst D.P.A D.P.A * snd D.P.A D.P.A :=
      congrArg (fst D.P.A D.P.A * ·) (_root_.mul_one _)
    simp [q0, q1, q2, q3, GlobalTheory.PolDeg.lamPts, Oε]
    generalize h (fst D.P.A D.P.A * snd D.P.A D.P.A).left = A, h (fst D.P.A D.P.A).left = A₁,
      h (snd D.P.A D.P.A).left = A₂, h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left = A₀
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨u, hu, hval⟩ := exists_gen D.P.isLB hF (prodGen _ _ e g) (isGen_prodGen _ _ e g hg)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [hval _ _ z J hJ, val_prodGen _ _ e g _ hJ, ← Finset.prod_mul_distrib]
  have : ∀ j, val (g j) (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J ^ e j *
      val (D.tau a (c j • b)) (𝟙 _) z J ^ e j = val (D.tau a b) (𝟙 _) z J ^ (e j * c j) := fun j => by
    rw [← mul_zpow, mul_comm, hv j a b z J hJ, ← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun j _ => this j, prod_zpow_sum, hec, zpow_one]

end GlobalTheory.Mum.LamComb
