import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMarginStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealBilinFormEqSumAdditiveImageIntFormsStatement

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.ConeSpan

theorem exists_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 →
      0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation M hM

theorem exists_rat_span {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := GlobalTheory.T.exists_realBilinForm_eq_sum_additive_image_intForms B

theorem free_finite_int (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (X₁ : Type)
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] :
    Module.Free ℤ X₁ ∧ Module.Finite ℤ X₁ := by
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  refine ⟨?_, this⟩
  have : Module.IsTorsionFree O X₁ := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree ℤ X₁ :=
    Module.IsTorsionFree.comap (S := O) (Int.castRingHom O)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have : r = 0 := by simpa using h0
        subst this
        exact (not_isRegular_zero (R := ℤ)) hr))
      (fun r m => Int.cast_smul_eq_zsmul O r m)
  exact Module.free_of_finite_type_torsion_free'

theorem nonneg_of_near {ι L : Type} [Fintype ι] [AddCommGroup L] (b : Module.Basis ι ℤ L)
    {B₁ : L →ₗ[ℤ] L →ₗ[ℤ] ℝ} (h : IsPosDef B₁) : ∃ η : ℝ, 0 < η ∧ ∀ (P : LinearMap.BilinForm ℤ L) (D : ℝ), 0 < D →
      (∀ i j, |(P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)| ≤ η) → ∀ x, 0 ≤ P x x := by
  obtain ⟨η, hη, hE⟩ := exists_margin (fun i j => B₁ (b i) (b j)) ((isPosDef_iff_basis b B₁).1 h)
  refine ⟨η, hη, fun P D hD hP x => ?_⟩
  have hP' : IsPosDef (toReal P) := (isPosDef_iff_basis b _).2 fun c hc => by
    have h1 := hE (fun i j => (P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)) hP c hc
    simp only [add_sub_cancel] at h1
    simp only [toReal_apply]
    have e : ∑ i, ∑ j, c i * c j * ((P (b i) (b j) : ℝ) / D) = (∑ i, ∑ j, c i * c j * (P (b i) (b j) : ℝ)) / D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    exact (div_pos_iff_of_pos_right hD).1 h1
  have := hP'.nonneg x
  simpa using this

theorem exists_nonneg_comb_of_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hB : B ∈ psdCone bar X) : ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hpos, hBr⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_finite_int O X₁
  let b := Module.Free.chooseBasis ℤ X₁
  obtain ⟨η, hη, hnear⟩ := nonneg_of_near b hpos
  obtain ⟨n, w, Q, hw, hg⟩ := exists_rat_span B₁
  have hwv : ∀ y z, B₁ y z = ∑ k, w k * (Q k y z : ℝ) := fun y z => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hw y z
  have hQ : ∀ k, Q k ∈ balForms bar X₁ := fun k => by
    obtain ⟨g, hg⟩ := hg k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · exact_mod_cast (hg y z).trans ((congrArg g (hB₁.1 y z)).trans (hg z y).symm)
    · exact_mod_cast (hg _ _).trans ((congrArg g (hB₁.2 a y z)).trans (hg _ _).symm)
  set K : ℝ := ∑ k, ∑ i, ∑ j, |(Q k (b i) (b j) : ℝ)| with hK
  have hKsum : ∀ i j, ∑ k, |(Q k (b i) (b j) : ℝ)| ≤ K := fun i j => Finset.sum_le_sum fun k _ =>
    (Finset.single_le_sum (f := fun j => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |(Q k (b i) (b j) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hKle : ∀ k i j, |(Q k (b i) (b j) : ℝ)| ≤ K := fun k i j =>
    (Finset.single_le_sum (f := fun k => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (hKsum i j)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * (n + 1) * K / η)
  have hDpos : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
  have hDK : 2 * (n + 1) * K ≤ D * η := by rw [div_lt_iff₀ hη] at hD; linarith
  set a : Fin n → ℤ := fun k => ⌊(D : ℝ) * w k⌋ with ha
  set δ : Fin n → ℝ := fun k => D * w k - a k with hδ
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.2 (Int.floor_le _)
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    have := Int.lt_floor_add_one ((D : ℝ) * w k)
    simp only [hδ, ha]; linarith
  set R : LinearMap.BilinForm ℤ X₁ := ∑ k, a k • Q k with hR
  have hRv : ∀ y z, (R y z : ℝ) = D * B₁ y z - ∑ k, δ k * (Q k y z : ℝ) := fun y z => by
    simp only [hR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, hwv,
      Finset.mul_sum, ← Finset.sum_sub_distrib, hδ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hSb : ∀ i j, |∑ k, δ k * (Q k (b i) (b j) : ℝ)| ≤ K := fun i j =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (hδ0 k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hδ1 k)).trans (hKsum i j))
  have hRnn : ∀ x, 0 ≤ R x x := hnear R D hDpos fun i j => by
    rw [hRv, show (D * B₁ (b i) (b j) - ∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D - B₁ (b i) (b j) =
      -(∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D by field_simp; ring, abs_div, abs_neg, abs_of_pos hDpos,
      div_le_iff₀ hDpos]
    nlinarith [hSb i j]
  let N : ℤ := n + 1
  have hQnn : ∀ k x, 0 ≤ (R + N • Q k) x x := fun k => hnear _ D hDpos fun i j => by
    have e : ((R + N • Q k) (b i) (b j) : ℝ) / D - B₁ (b i) (b j) =
        (N * (Q k (b i) (b j) : ℝ) - ∑ l, δ l * (Q l (b i) (b j) : ℝ)) / D := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, hRv]
      field_simp; ring
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have h1 := abs_sub (N * (Q k (b i) (b j) : ℝ)) (∑ l, δ l * (Q l (b i) (b j) : ℝ))
    rw [abs_mul] at h1
    have h2 : |(N : ℝ)| = n + 1 := by simp [N]; positivity
    rw [h2] at h1
    nlinarith [hSb i j, hKle k i j]
  let γ₁ : Fin (n + 1) → LinearMap.BilinForm ℤ X₁ := Fin.cons R fun k => R + N • Q k
  let c : Fin (n + 1) → ℝ := Fin.cons ((1 + ∑ k, (1 - δ k)) / (N * D)) fun k => δ k / (N * D)
  have hN : (0 : ℝ) < N := by simp [N]; positivity
  refine ⟨n + 1, fun i => pull r (γ₁ i), c, fun i => pull_mem r ?_, fun i y => ?_, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) i
    · exact (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k) : R ∈ _)
    · show R + N • Q k ∈ _
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k))
        (Submodule.smul_mem _ _ (hQ k))
  · simp only [pull_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hRnn _
    · exact hQnn k _
  · refine Fin.cases ?_ (fun k => ?_) i
    · refine div_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => sub_nonneg.2 (hδ1 k))) (by positivity)
    · exact div_nonneg (hδ0 k) (by positivity)
  · refine LinearMap.ext₂ fun y z => ?_
    simp only [hBr, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul,
      Fin.sum_univ_succ, γ₁, c, Fin.cons_zero, Fin.cons_succ, LinearMap.add_apply, Int.cast_add, Int.cast_mul]
    rw [hRv]
    set u := B₁ (r y) (r z)
    set S := ∑ k, δ k * (Q k (r y) (r z) : ℝ)
    have e1 : ∑ k, δ k / (N * D) * (D * u - S + N * (Q k (r y) (r z) : ℝ)) =
        (∑ k, δ k) * (D * u - S) / (N * D) + S / D := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have e2 : ∑ k, (1 - δ k) = n - ∑ k, δ k := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e1, e2]
    have hN' : (N : ℝ) = n + 1 := by simp [N]
    rw [hN']
    field_simp
    ring

end GlobalTheory.PolFan.ConeSpan
