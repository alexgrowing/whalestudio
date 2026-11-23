import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfMemKG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open GlobalTheory.Orb
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.PsCo.NonEll

theorem isRegSS_conj {n : ℕ} {ε : Fin n → Bool} (s x : UJ ε) (hs : IsRegSS (ujMat ε s)) :
    IsRegSS (ujMat ε (x⁻¹ * s * x)) := by
  unfold IsRegSS at hs ⊢
  rw [map_mul, Matrix.charpoly_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel,
    one_mul]
  exact hs

theorem isCompact_cent_of_conj {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (s x : G) (h : IsCompact (cent (x⁻¹ * s * x) : Set G)) : IsCompact (cent s : Set G) := by
  have hc : Continuous fun y : G => x * y * x⁻¹ := by fun_prop
  have := h.image hc
  convert this using 1
  ext y
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_image]
  constructor
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    calc x⁻¹ * y * x * (x⁻¹ * s * x) = x⁻¹ * (y * s) * x := by group
      _ = x⁻¹ * (s * y) * x := by rw [hy]
      _ = x⁻¹ * s * x * (x⁻¹ * y * x) := by group
  · rintro ⟨z, hz, rfl⟩
    calc x * z * x⁻¹ * s = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by rw [hz]
      _ = s * (x * z * x⁻¹) := by group

theorem stNonEll : GlobalTheory.PsCo.Pc1.StNonEll := by
  intro n ε s hs hnc
  set r : UJ ε → ℝ := fun g => rM ε (toM g) with hr
  have hcont : Continuous r := (GlobalTheory.offDiagBlockNorm_cont_inv n ε).1
  have hsub : IsCompact {g : UJ ε | r g ≤ r s} := GlobalTheory.isCompact_offDiag_sublevel n ε (r s)
  have hcl : IsClosed (Set.range fun x : UJ ε => x⁻¹ * s * x) := isClosed_class_realUJ hs
  have hK := hsub.inter_right hcl
  have hne : ({g : UJ ε | r g ≤ r s} ∩ Set.range fun x : UJ ε => x⁻¹ * s * x).Nonempty :=
    ⟨s, le_refl (r s), 1, by simp⟩
  obtain ⟨g, ⟨hg1, x₀, rfl⟩, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨r (x₀⁻¹ * s * x₀), ?_, fun x => ?_⟩
  · have h0 : 0 ≤ r (x₀⁻¹ * s * x₀) := Finset.sum_nonneg fun z _ => by positivity
    refine lt_of_le_of_ne h0 fun h => hnc ?_
    have hk : x₀⁻¹ * s * x₀ ∈ KG ε := (GlobalTheory.offDiag_zero_iff_mem_K n ε _).1 h.symm
    exact isCompact_cent_of_conj s x₀ (GlobalTheory.isCompact_cent_of_mem_KG n ε _ hk (isRegSS_conj s x₀ hs))
  · change r (x₀⁻¹ * s * x₀) ≤ r (x⁻¹ * s * x)
    by_cases hx : r (x⁻¹ * s * x) ≤ r s
    · exact hmin ⟨hx, x, rfl⟩
    · exact le_trans hg1 (not_le.1 hx).le

end GlobalTheory.PsCo.NonEll
