import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralChangeOfVariablesIntMatrixSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionMatrixMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromIFinsetSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosetsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlRepresentativesRightMulPermStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixNormalizesGammaOneGammaZeroLevelStatement

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HeckeEqv

theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  simp [toGL, hA, hB, hAB, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  ext i j
  simp [toGL, h, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.SpecialLinearGroup.mapGL]

theorem toGL_smul_mat (γ : SL(2, ℤ)) (τ : ℍ) : toGL (mat γ) • τ = γ • τ := by
  rw [toGL_mat]; rfl

theorem mem_of_natDegree_le {w : ℕ} {p : ℂ[X]} (h : p.natDegree ≤ w) : p ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => mem_of_natDegree_le ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  refine Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_pow_le (p := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) (n := i)).trans
    (Nat.mul_le_mul_left i (natDegree_linear_le))
  have h2 := (natDegree_pow_le (p := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) (n := w - i)).trans
    (Nat.mul_le_mul_left (w - i) (natDegree_linear_le))
  omega

theorem hecke_eqv (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk2 : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (hδ : ∀ i, 0 < (δ i).det)
    (hπ : ∀ γ : Γ, ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) :
    per Γ (k - 2) (hkF (k : ℤ) δ ⇑f) - hk Γ (k - 2) δ (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2) := by
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑f := f.holo'
  have hdet : ∀ i, (δ i).det ≠ 0 := fun i => (hδ i).ne'
  have hpc := (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 f).2
  set w := k - 2 with hw
  set F := eichler w ⇑f with hF
  set c : ι → ℂ[X] := fun i => slP w (δ i) (F (toGL (δ i) • UpperHalfPlane.I)) with hc
  set C := ∑ i, c i with hCdef
  have hC : -C ∈ degreeLT ℂ (w + 1) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => polySlash_mem _ _ _)
  refine ⟨⟨-C, hC⟩, ?_⟩
  funext γ
  have hγdet : (mat (γ : SL(2, ℤ))).det ≠ 0 := by simp [mat]
  obtain ⟨hex⟩ : Nonempty (∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) := ⟨hπ γ⟩
  have e2 : hk Γ w δ (per Γ w ⇑f) γ =
      ∑ i, slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) := by
    simp only [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  have e1 : per Γ w (hkF (k : ℤ) δ ⇑f) γ =
      ∑ i, (slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) - slP w (mat γ) (c i)) := by
    simp only [per, hkF]
    rw [GlobalTheory.T.eichlerIntegralFromI_finset_sum w _ (fun i => hfd.slash _ _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash k hk2 ⇑f hfd (δ i) (hδ i) ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
    rw [eq_sub_of_add_eq h.symm, map_sub, GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (δ i) (mat γ) _ (eichler_mem _ _ _),
      toGL_mul _ _ (hdet i) hγdet, mul_smul, toGL_smul_mat]
  have e3 : ∀ i, slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) =
      slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) + c (hex.choose i) := by
    intro i
    set γ' := (hex.choose_spec i).choose
    have hγ' : δ i * mat γ = mat γ' * δ (hex.choose i) := (hex.choose_spec i).choose_spec
    have hγ'det : (mat (γ' : SL(2, ℤ))).det ≠ 0 := by simp [mat]
    rw [hγ', toGL_mul _ _ hγ'det (hdet _), mul_smul, toGL_smul_mat,
      GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (mat γ') (δ (hex.choose i)) _ (eichler_mem _ _ _),
      hpc γ' (toGL (δ (hex.choose i)) • UpperHalfPlane.I), map_sub]
    simp only [hc]
    abel
  have hsum : ∑ i, c (hex.choose i) = C := Equiv.sum_comp hex.choose c
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply]
  rw [e1, e2]
  simp only [e3, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← map_sum, map_neg]
  abel

theorem tqFam_det (q : ℕ) (hq : q.Prime) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : 0 < (tqFam q σ i).det := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  unfold tqFam
  split_ifs
  · simpa [Matrix.det_fin_two_of] using hq0
  · simpa [Matrix.det_mul, mat, dg, Matrix.det_fin_two_of] using hq0

theorem ulFam_det (l : ℕ) (hl : l.Prime) (i : Fin l) : 0 < (ulFam l i).det := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl.pos
  simpa [ulFam, Matrix.det_fin_two_of] using hl0

theorem period_map_equivariant : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ f : ModularForm (Lev N l) (k : ℤ),
  (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
    per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) ∧
  per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2) ∧
  (∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    per (Lev N l) (k - 2) (DdF (k : ℤ) σ ⇑f) - DdZ (Lev N l) (k - 2) σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) := by
  intro N l k hN hl hlN hk f
  refine ⟨fun q σ hq hqN hσ => ?_, ?_, fun d σ hσ => ?_⟩
  · exact hecke_eqv _ k (by omega) f (tqFam q σ) (tqFam_det q hq σ)
      (GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets N l q hN hl hlN hq hqN σ hσ)
  · exact hecke_eqv _ k (by omega) f (ulFam l) (ulFam_det l hl) (GlobalTheory.T.heckeUlRepresentatives_right_mul_perm N l hN hl hlN)
  · exact hecke_eqv _ k (by omega) f (fun _ : Unit => mat σ) (fun _ => by simp [mat])
      (fun γ => ⟨Equiv.refl _, fun _ => GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel N l d σ hσ γ⟩)

end GlobalTheory.HeckeFamilyMatrices.HeckeEqv
