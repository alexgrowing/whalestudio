import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo

private theorem norm_apply_le_one_of_conjTranspose_mul_self {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (i j : Fin n) : ‖U i j‖ ≤ 1 := by
  have h := congrFun (congrFun hU j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.one_re] at hre
  have hterm : ∀ x, (star (U x j) * U x j).re = ‖U x j‖ ^ 2 := fun x => by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    ring
  simp only [hterm] at hre
  have hle : ‖U i j‖ ^ 2 ≤ 1 := by
    rw [← hre]
    exact Finset.single_le_sum (f := fun x => ‖U x j‖ ^ 2) (fun x _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (U i j)]

private theorem isCompact_unitary_commute_Jm_inUJ (n : ℕ) (ε : Fin n → Bool) :
    IsCompact {M : Matrix (Fin n) (Fin n) ℂ |
      M ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ M * Jm ε = Jm ε * M ∧ inUJ ε M} := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * M = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have h2 : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M * Mᴴ = 1} :=
      isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
    have h3 : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M * Jm ε = Jm ε * M} :=
      isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id)
    have h4 : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * Jm ε * M = Jm ε} :=
      isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    have e : {M : Matrix (Fin n) (Fin n) ℂ |
        M ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ M * Jm ε = Jm ε * M ∧ inUJ ε M} =
        ({M | Mᴴ * M = 1} ∩ {M | M * Mᴴ = 1}) ∩ ({M | M * Jm ε = Jm ε * M} ∩ {M | Mᴴ * Jm ε * M = Jm ε}) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Unitary.mem_iff, Matrix.star_eq_conjTranspose, inUJ,
        and_assoc]
    rw [e]
    exact (h1.inter h2).inter (h3.inter h4)
  · intro M hM
    rw [Set.mem_univ_pi]
    intro i
    rw [Set.mem_univ_pi]
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_apply_le_one_of_conjTranspose_mul_self (U := M)
      (Unitary.star_mul_self_of_mem hM.1) i j

theorem isCompact_KG_set : ∀ (n : ℕ) (ε : Fin n → Bool),
    IsCompact ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)) := by
  intro n ε
  haveI : CompactSpace {M : Matrix (Fin n) (Fin n) ℂ |
      M ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ M * Jm ε = Jm ε * M ∧ inUJ ε M} :=
    isCompact_iff_compactSpace.mp (isCompact_unitary_commute_Jm_inUJ n ε)
  let φ : {M : Matrix (Fin n) (Fin n) ℂ |
      M ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ M * Jm ε = Jm ε * M ∧ inUJ ε M} → S7.UJ ε := fun M =>
    ⟨⟨M.1, star M.1, Unitary.mul_star_self_of_mem M.2.1, Unitary.star_mul_self_of_mem M.2.1⟩, M.2.2.2⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  have hrange : Set.range φ = ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)) := by
    ext g
    constructor
    · rintro ⟨M, rfl⟩
      exact And.intro M.2.1 M.2.2.1
    · intro hg
      have hg' : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Jm ε =
            Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := hg
      refine ⟨⟨((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ), hg'.1, hg'.2, g.2⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  rw [← hrange]
  exact isCompact_range hφ

end GlobalTheory.CompanionTheory.UGeo
