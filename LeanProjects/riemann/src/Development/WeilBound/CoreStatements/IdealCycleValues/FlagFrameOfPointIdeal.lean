import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProjIdealIndependentOfBasis
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

theorem foldr_diffStep_zero {K : Type} (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) (h : (K → ℤ) → ℤ) :
    l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with hb | hb
    · subst hb
      funext m
      simp [diffStep]
    · rw [ih hb]
      funext m
      simp [diffStep]

theorem intNumL_of_zero_mem {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (V : Ideal (MRing ι F)) (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) : intNumL F V l = 0 := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, foldr_diffStep_zero l hl]
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    exact hm.symm
  · rfl

theorem flag_frame_of_point_ideal : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hd N w b hw a ha Y hY
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact Finset.sum_eq_zero fun α hα => by
      rw [Finset.Nat.mem_antidiagonalTuple] at hα
      simp at hα
  have ht : AlgebraicIndependent Ω
      ((IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω))) ∘ X) :=
    (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
      (IsFractionRing.injective (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω)))
  have h1 := hS F Ω K ι y e hP hd N hN _ _ w b hw N 0 _ (isTwistedDualGens_triv F y N) _ _ ht
    (N - 1 + a) Y (by omega)
  have h2 := hS F Ω K ι y e hP hd N hN _ _ _ _ (isFlagFrame_scaledTriv F y N (one_ne_zero (α := Ω))) N 0 _
    (isTwistedDualGens_triv F y N) _ _ ht (N - 1 + a) Y (by omega)
  rw [projIdeal_independent_of_basis F Ω K ι y N N _ w (scaledBasis N (one_ne_zero (α := Ω))) _ _ _ ht, h2,
    if_pos (Nat.le_add_right _ _), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at h1
  simp only [zero_sub] at h1
  rw [← h1]
  refine Finset.sum_eq_zero fun α hα => intNumL_of_zero_mem _ _ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  refine List.mem_append_left _ ?_
  unfold rootList
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_replicate.mpr ⟨hi, by simp⟩⟩

end BaseChangeColon
