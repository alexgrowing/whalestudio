import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.JFrac

open MvPolynomial

theorem exists_rs_eq_pow_mul {X : Scheme} {U V : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : X.basicOpen f = V) (h : V ≤ U) (b : Γ(X, V)) :
    ∃ (M : ℕ) (a : Γ(X, U)), rs X h a = rs X h f ^ M * b := by
  subst hV
  obtain ⟨M, a, ha⟩ :=
    exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU.isCompact hU.isQuasiSeparated f b
  exact ⟨M, a, ha⟩

theorem exists_form : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (i j : Fin (n + 1)) (c : Γ((Y e).left, C.D e i ⊓ C.D e j)), c ∈ towerIdeal Y e (I ^ e) _ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ k : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (k + 2 * N) ∧ (∀ m, MvPolynomial.coeff m F ∈ I ^ e) ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ N * c := by
  intro R _ I Y β hP n C e i j c hc
  obtain ⟨hbasic, -, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hP n C
  obtain ⟨-, hsurj⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hP n C
  have hVU : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hX : ∀ l, C.ev e i (X l) = C.ρ e i l := fun l => by simp [Charts.ev]
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) := Ideal.map MvPolynomial.C (I ^ e)
  let S : Ideal Γ((Y e).left, C.D e i ⊓ C.D e j) :=
    { carrier := {c | ∃ N₁ : ℕ, ∃ G ∈ J,
        rs (Y e).left hVU (C.ev e i G) = rs (Y e).left hVU (C.ρ e i j) ^ N₁ * c}
      add_mem' := by
        rintro a b ⟨N₁, G, hG, h1⟩ ⟨N₂, G', hG', h2⟩
        refine ⟨N₁ + N₂, X j ^ N₂ * G + X j ^ N₁ * G',
          J.add_mem (J.mul_mem_left _ hG) (J.mul_mem_left _ hG'), ?_⟩
        simp only [map_add, map_mul, map_pow, hX, h1, h2]
        ring
      zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro b a ⟨N₁, G, hG, h1⟩
        obtain ⟨M, a', ha'⟩ := exists_rs_eq_pow_mul (C.aff e i) (C.ρ e i j) (hbasic e i j) hVU b
        obtain ⟨H, rfl⟩ := hsurj e i a'
        refine ⟨M + N₁, H * G, J.mul_mem_left _ hG, ?_⟩
        simp only [map_mul, ha', h1, smul_eq_mul]
        ring }
  have hcS : c ∈ S := by
    refine (Ideal.map_le_iff_le_comap.2 (fun r hr => ?_)) hc
    refine ⟨0, MvPolynomial.C r, Ideal.mem_map_of_mem _ hr, ?_⟩
    simp [Charts.ev, rs_cst]
  obtain ⟨N₁, G, hG, hN₁⟩ := hcS
  have hGc : ∀ d, homogeneousComponent d G ∈ J := fun d => by
    refine MvPolynomial.mem_map_C_iff.2 fun m => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact MvPolynomial.mem_map_C_iff.1 hG m
    · exact (I ^ e).zero_mem
  have hfix : ∀ d t, C.ρ e i i ^ t * C.ev e i (homogeneousComponent d G) =
      C.ev e i (homogeneousComponent d G) := fun d t => by
    have h1 := (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hP n C e d (homogeneousComponent d G)
      (homogeneousComponent_isHomogeneous d G) (MvPolynomial.mem_map_C_iff.1 (hGc d)) i i).2.1
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ (C.ρ e i i) t, mul_assoc, h1, ih]
  refine ⟨N₁ + G.totalDegree, fun N hN k => ?_⟩
  refine ⟨X j ^ (N - N₁) * ∑ d ∈ Finset.range (G.totalDegree + 1),
      X i ^ (k + N + N₁ - d) * homogeneousComponent d G, ?_, ?_, ?_⟩
  · have hdeg : k + 2 * N = (N - N₁) + (k + N + N₁) := by omega
    rw [hdeg]
    refine (isHomogeneous_X_pow _ _).mul (IsHomogeneous.sum _ _ _ fun d hd => ?_)
    have hd' : d ≤ k + N + N₁ := by
      have := Finset.mem_range.1 hd
      omega
    have := (isHomogeneous_X_pow i (k + N + N₁ - d)).mul (homogeneousComponent_isHomogeneous d G)
    rwa [Nat.sub_add_cancel hd'] at this
  · exact MvPolynomial.mem_map_C_iff.1
      (J.mul_mem_left _ (J.sum_mem fun d _ => J.mul_mem_left _ (hGc d)))
  · have hsum : C.ev e i (∑ d ∈ Finset.range (G.totalDegree + 1),
        X i ^ (k + N + N₁ - d) * homogeneousComponent d G) = C.ev e i G := by
      rw [map_sum]
      conv_rhs => rw [← sum_homogeneousComponent G, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, map_pow, hX, hfix]
    rw [map_mul, hsum, map_mul, hN₁, map_pow, map_pow, hX, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (by omega : N₁ ≤ N)]

end GlobalTheory.FormalAlg.JFrac
