import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorContentIdealNormProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormWittColumnTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameFirstColumnNonzeroOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHeightUniformLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormWeightedCountBoundStatement

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisMidHt

theorem tsum_ht_add_smul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ s : ℝ, 2 < s → ∃ C : ℝ, ∀ y : Fin n → E, y ≠ 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn X) y = 0 →
        hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
        ∑' c : E, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (y + c • GlobalTheory.EisMidHt.firstColumn X)) ^ (-s)) ≤
          ENNReal.ofReal C * ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y) ^ (1 - s)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS s hs
  obtain ⟨hCM, -, hJ, -, hW, hA, -⟩ := hS
  obtain ⟨hx0, hsplit⟩ := GlobalTheory.T.witt_frame_first_column_nonzero_orthogonal F E σ n J r X Y L a hCM hJ hW hA
  obtain ⟨δ, hδ, hlow, hpos⟩ := GlobalTheory.T.lattice_height_uniform_lower_bound F E σ n L a hCM hA.lat
  obtain ⟨Ix, hIx0, hIxm, -⟩ := GlobalTheory.T.lattice_vector_content_ideal_norm_product F E n L hA.lat (firstColumn X) hx0
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.ideal_norm_weighted_count_bound F E σ hCM Ix hIx0
    (fun w => normInf a w (fun i => compInf F E w (adVec F (firstColumn X) i))) (fun w => hpos _ hx0 w) s hs δ hδ
  refine ⟨δ⁻¹ + max C₁ 0, fun y hy0 hyx hyy => ?_⟩
  obtain ⟨hne, hmem⟩ := hsplit y hyx hyy
  obtain ⟨Iy, -, hIym, hIyn⟩ := GlobalTheory.T.lattice_vector_content_ideal_norm_product F E n L hA.lat y hy0
  have hHy : ht L a (adVec F y) = (FractionalIdeal.absNorm Iy : ℝ) *
      ∏ w, normInf a w (fun i => compInf F E w (adVec F y i)) := by
    rw [← hIyn]; rfl
  have hterm : ∀ c : {c : E // c ≠ 0}, ht L a (adVec F (y + (c : E) • firstColumn X)) =
      (FractionalIdeal.absNorm (Iy ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * Ix) : ℝ) *
        ∏ w, (normInf a w (fun i => compInf F E w (adVec F y i)) +
          ‖Algebra.norm w.Completion (inclR (F := F) w.Completion (c : E))‖ *
            normInf a w (fun i => compInf F E w (adVec F (firstColumn X) i))) := by
    rintro ⟨c, hc⟩
    obtain ⟨I', -, hI'm, hI'n⟩ := GlobalTheory.T.lattice_vector_content_ideal_norm_product F E n L hA.lat (y + c • firstColumn X) (hne c hy0)
    have heq : I' = Iy ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c⁻¹ * Ix := by
      ext l
      rw [hI'm, hmem, ← hIym, ← hIxm]
      show _ ↔ l ∈ ((Iy ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c⁻¹ * Ix :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E)
      rw [FractionalIdeal.coe_inf, Submodule.mem_inf, FractionalIdeal.mem_coe, FractionalIdeal.mem_coe,
        FractionalIdeal.mem_singleton_mul]
      refine and_congr_right fun _ => ⟨fun h => ⟨l * c, h, by field_simp⟩, ?_⟩
      rintro ⟨z, hz, rfl⟩
      rwa [mul_right_comm, inv_mul_cancel₀ hc, one_mul]
    have e1 : ht L a (adVec F (y + c • firstColumn X)) =
        (∏ᶠ v, (normFin F L v (fun i => compFin F E v (adVec F (y + c • firstColumn X) i)) : ℝ)) *
          ∏ w, normInf a w (fun i => compInf F E w (adVec F (y + c • firstColumn X) i)) := rfl
    rw [e1, hI'n, heq]
    exact congrArg _ (Finset.prod_congr rfl fun w _ => GlobalTheory.T.archimedean_norm_witt_column_translate F E σ n J r X Y L a hCM hJ hW hA y hyy c w)
  have hH0 : δ ≤ (FractionalIdeal.absNorm Iy : ℝ) * ∏ w, normInf a w (fun i => compInf F E w (adVec F y i)) :=
    hHy ▸ hlow y hy0
  have hsum := hC₁ Iy (fun w => normInf a w (fun i => compInf F E w (adVec F y i))) (fun w => (hpos y hy0 w).le) hH0
  set H := (FractionalIdeal.absNorm Iy : ℝ) * ∏ w, normInf a w (fun i => compInf F E w (adVec F y i)) with hHdef
  have hHpos : 0 < H := lt_of_lt_of_le hδ hH0
  rw [hHy]
  have hsplit2 : ∑' c : E, ENNReal.ofReal (ht L a (adVec F (y + c • firstColumn X)) ^ (-s)) =
      ENNReal.ofReal (ht L a (adVec F (y + (0 : E) • firstColumn X)) ^ (-s)) +
        ∑' c : {c : E // c ≠ 0}, ENNReal.ofReal (ht L a (adVec F (y + (c : E) • firstColumn X)) ^ (-s)) := by
    rw [← ENNReal.summable.tsum_add_tsum_compl (s := ({0} : Set E)) ENNReal.summable,
      tsum_singleton (0 : E) (fun c : E => ENNReal.ofReal (ht L a (adVec F (y + c • firstColumn X)) ^ (-s)))]
    rfl
  rw [hsplit2, zero_smul, add_zero, hHy]
  simp_rw [hterm]
  have h0 : ENNReal.ofReal (H ^ (-s)) ≤ ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (H ^ (1 - s)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : H ^ (1 - s) = H ^ (-s) * H := by
      rw [show 1 - s = -s + 1 by ring, Real.rpow_add hHpos, Real.rpow_one]
    rw [e, ← mul_assoc, mul_comm δ⁻¹, mul_assoc]
    have hp : 0 < H ^ (-s) := Real.rpow_pos_of_pos hHpos _
    have : 1 ≤ δ⁻¹ * H := by rw [le_inv_mul_iff₀ hδ, mul_one]; exact hH0
    nlinarith
  calc _ ≤ ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (H ^ (1 - s)) + ENNReal.ofReal C₁ * ENNReal.ofReal (H ^ (1 - s)) :=
        add_le_add h0 hsum
    _ ≤ ENNReal.ofReal (δ⁻¹ + max C₁ 0) * ENNReal.ofReal (H ^ (1 - s)) := by
        rw [ENNReal.ofReal_add (inv_nonneg.2 hδ.le) (le_max_right _ _), add_mul]
        gcongr
        exact le_max_left _ _

end GlobalTheory.EisMidHt

end
