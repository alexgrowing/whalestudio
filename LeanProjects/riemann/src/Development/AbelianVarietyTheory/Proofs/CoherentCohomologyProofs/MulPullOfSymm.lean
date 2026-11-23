import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.MulPullAny

open GlobalTheory.MulPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem iso_of_hasGen {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} {m : ℤ}
    (h : HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -m]) :
    ∃ w : LB.Iso (AbLaw.pw L m) (L.pull F), w.IsGen := by
  obtain ⟨t, ht⟩ := h
  have le : ∀ p : (PUnit → L.ι) × L.ι, (L.pull F).U p.1 ⊓ L.U p.2 ≤
      LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] := fun p y hy => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [mem_pull.1 hy.1, hy.2]
  refine ⟨⟨fun p => res (le p) (t.s ![p.1 PUnit.unit, p.2])⟩, (isGen_iff _).2 ?_⟩
  intro Y f y j j' k k' hj hj' hk hk'
  have m₁ : f y ∈ (L.pull F).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  have m₂ : f y ∈ (L.pull F).U (fun _ => j') ⊓ L.U k' := ⟨mem_pull.2 hj', hk'⟩
  refine (gm_res f y (le (fun _ => j, k)) m₁ _).trans
    ((gen_trans ht f y (le (fun _ => j, k) m₁) (le (fun _ => j', k') m₂)).trans
      (congrArg₂ (· * ·) ?_ (gm_res f y (le (fun _ => j', k')) m₂ _).symm))
  rw [trF, Fin.prod_univ_two]
  simp only [Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  exact congrArg (fun u => _ * u⁻¹) (map_zpow (gm f y (L.U k ⊓ L.U k')) (L.g k k') m).symm

theorem mulPull_of_symm : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ H : LB B.left, H.IsLB → (∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen) → ∀ n : ℕ, ∃ w : LB.Iso (pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (mulA B n).left), w.IsGen := by
  intro K _ _ B _ hB H hH ⟨w, hw⟩ n
  have := hB.comm
  have hcube : HasGen H (thφ B (x3 B)) thε := GlobalTheory.exists_gen_theta_of_isAbelianScheme K B hB H hH
  have hrig : HasGen H (K := PUnit) (fun _ => eSec B) (fun _ => 1) :=
    DVR.exists_gen_of_local (V := K) H hH _ _
  have hneg : HasGen H (K := Fin 2) ![𝟙 B.left ≫ (GrpObj.inv : B ⟶ B).left, 𝟙 B.left] ![1, -1] :=
    Geo.Tor.gen_of_iso ((Geo.Tor.isGen_iff w).1 hw) _
  have main : HasGen H (K := Fin 2) ![(𝟙 B : B ⟶ B).left, ((𝟙 B : B ⟶ B) ^ n).left] ![(n : ℤ) ^ 2, -1] := by
    refine hasGen_pow hH hcube (𝟙 B) ?_ ?_ n
    · refine (hrig.pull (toUnit B).left).of_formEq hH (fun U _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hH (fun U _ h => ?_)
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        neg_neg, _root_.mul_one]
      exact _root_.mul_comm _ _
  refine iso_of_hasGen (main.inv.of_formEq hH (fun U _ h => ?_))
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    neg_neg, _root_.mul_one, Nat.cast_pow]
  exact _root_.mul_comm _ _

end GlobalTheory.MulPullAny
