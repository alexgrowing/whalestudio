import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open Classical in

private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
    let b := Module.finBasis ℚ D.what₂.LL
    obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
      (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
      ((Set.finite_range _).union (Set.toFinite _)) (by
        rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
        · exact mem_algebraicClosure_iff.2
            ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
        · exact hdata.2.1
        · exact hdata.2.2
        · exact hwp)
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
