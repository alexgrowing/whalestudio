import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibresStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimDense

theorem exists_gen_cube_eSec {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (u : A ⟶ A) [IsMonHom u] : ∃ c : ((cubeLB A ![𝟙 A, u] L).pull (eSec A)).Gen, c.IsGen := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  have key : ∀ I, η[A] ≫ psum A ![𝟙 A, u] I = η[A] := fun I => by
    refine (psum_hom (preHom (G := A) η[A]) _ I).trans ?_
    have : (fun i => preHom (G := A) η[A] (![𝟙 A, u] i)) = fun i => (1 : (A ⟶ A) →* (𝟙_ (Over S) ⟶ A)) (![𝟙 A, u] i) := by
      funext i
      fin_cases i
      · exact (Category.comp_id _).trans e₁.symm
      · exact (IsMonHom.one_hom u).trans e₁.symm
    rw [this, ← psum_hom]
    exact e₁
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun _ : ULift.{0} (Finset (Fin 2)) => eSec A)
    (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ k => (Fintype.prod_empty _).trans (by
      have : ∑ I : ULift.{0} (Finset (Fin 2)), (-1 : ℤ) ^ (2 - I.down.card) = 0 := by decide
      have e := congrArg Additive.toMul (map_sum (zmultiplesHom (Additive U) (Additive.ofMul (k (eSec A))))
        (fun I : ULift.{0} (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)) Finset.univ)
      rw [this, map_zero, toMul_sum] at e
      exact e)) (LB.oneGen L (Y := (𝟙_ (Over S)).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact gen_chartPull (chartPullOut L _ _ (eSec A) _ fun I => congrArg (fun z => z.left) (key I.down).symm) t ht

end GlobalTheory.PrimDense

namespace GlobalTheory

theorem lbIso_cube_of_dense : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  intro hG S _ A _ _ L u hA hL hamp hrig hu hd
  have hM : (cubeLB A ![𝟙 A, u] L).IsLB := DVR.linComb_isLB _ hL _ _
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp S A.left (𝟙 _) (𝟙 _) A.hom (LB.div (cubeLB A ![𝟙 A, u] L) L)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (LB.isLB_div hM hL) (hd.mono ?_) (eSec A) (Over.w η[A]) ?_
  · rintro p ⟨K, _, x, G, _, _, φ, L', u', hp, h, hL', H, hu', H'⟩
    refine ⟨K, inferInstance, x, G.left, φ, G.hom, hp, h.1, ?_⟩
    have i : LBIso (cubeLB G ![𝟙 G, u'] L') ((cubeLB A ![𝟙 A, u] L).pull φ) := by
      obtain ⟨w, hw⟩ := H
      refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ _ fun I => ?_) (iso_linComb ((isGen_iff w).1 hw) _ _)
      refine psum_push h _ _ (Over.homMk φ h.1.w) (fun i => ?_) I.down
      fin_cases i
      exacts [Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm), Over.OverMorphism.ext hu']
    have a' : (cubeLB G ![𝟙 G, u'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    obtain ⟨w, hw⟩ := LBIso.trans (pull_isLB hL φ) hL' (pull_isLB hM φ) H.symm
      (LBIso.trans hL' a' (pull_isLB hM φ) H' i)
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw
  · obtain ⟨c, hc⟩ := hrig
    obtain ⟨c', hc'⟩ := PrimDense.exists_gen_cube_eSec hL u
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ c hc c' hc'
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw

end GlobalTheory
