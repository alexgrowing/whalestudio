import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LamIsoOfPairings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

theorem lam_iso_of_weil_pairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  intro hL k _ _ P P' α p d hα hp _ hW
  haveI : IsCommMonObj P.A := P.isAb.comm
  have fib : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (n : ℕ), 0 < n → n.Coprime p → x ^ n = 1 →
      ∃ t : LB.Gen ((LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))).pull
        (lift (toUnit P.A ≫ x) (𝟙 P.A)).left), t.IsGen := by
    intro x n hn hnp hx
    obtain ⟨u, hu, v⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) d n x hx
    obtain ⟨u', hu', v'⟩ := exists_gen_lam hL.globalFns hL.cube P' α 1 n x hx
    refine exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _ ?_
    refine lbIso_of_invariant P.isLB P'.isLB _ _ _ _ (Out.mulA P.A n).left
      (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
      (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
        obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
        exact ⟨a, b, c, e⟩) k P n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
      (fun y z J J' hJ hJ' => ?_)
    · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
        MonObj.comp_one, _root_.one_mul]
    · obtain ⟨c, hc, -⟩ := (hL.weil _ P n _).1 x y.1 hx y.2
      obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
        ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
          Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
      have e : unitOn (c ^ d) = unitOn c ^ d := map_pow (Units.map _) c d
      have h₁ := v y.1 (unitOn c) y.2 (by rw [Category.comp_id, Category.comp_id]; exact hc) z J hJ
      have h₂ := v' y.1 (unitOn (c ^ d)) y.2 (hW n x y.1 c hn hnp hx y.2 hc) z J' hJ'
      rw [pow_one, e] at h₂
      refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
      exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k P.A P.A (LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))) P.L
    P.isAb P.isAb P.isLB P.ample
    (LB.isLB_div (DVR.linComb_isLB _ (pull_isLB P'.isLB _) _ _)
      (DVR.linComb_isLB _ (DVR.linComb_isLB _ P.isLB _ _) _ _)) ?_ ?_ ?_
  · have := fib 1 1 one_pos (Nat.coprime_one_left p) (one_pow _)
    rwa [MonObj.comp_one] at this
  · refine (CoprimeTorsion.dense_torsion hL.ample hL.kerPow hL.irred k P hp).mono ?_
    exact Set.biUnion_subset_biUnion_left fun x ⟨n, hn, hnp, hx⟩ => fib x n hn hnp hx
  · obtain ⟨u, hu⟩ := exists_gen_axis (A := P.A) P.isLB (𝟙 _) d
    obtain ⟨u', hu'⟩ := exists_gen_axis (A := P.A) P'.isLB α.left 1
    exact exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _
      (lbIso_of_gens P.isLB P'.isLB _ _ _ _ u hu u' hu')

end GlobalTheory
