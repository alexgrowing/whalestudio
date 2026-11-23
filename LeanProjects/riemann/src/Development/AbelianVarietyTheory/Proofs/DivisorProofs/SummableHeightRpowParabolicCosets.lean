import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodementStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem summable_height_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  obtain ⟨lv, hlv⟩ := GlobalTheory.T.exists_leviSection_isotropicFrame F E σ n J j m C D Z J₀ hF
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hF.cm J L a
  choose p β hp k hk e using fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) =>
    hI ((q.out : ratPts σ J) * g)
  have h1 := GlobalTheory.T.summable_absDet_rational_points_godement F E σ n J j m C D Z J₀ hF lv hlv _
    (fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (q.out : ratPts σ J)) p
    (fun q => k q * g⁻¹) β _ (hK.image (continuous_mul_const g⁻¹)) (fun q => q.out.2)
    (fun q => (eq_mul_inv_of_mul_eq (e q)).trans (mul_assoc _ _ _)) (fun q => ⟨k q, hk q, rfl⟩) hp
    (fun q q' hq => ?_) t (by
      have h2 : (m : ℝ) + 2 * j = n := by exact_mod_cast hF.dim
      push_cast
      linarith)
  · refine h1.congr fun q => ?_
    rw [e, hh _ _ (hp q) _ (hk q)]
  · rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, Subgroup.mem_subgroupOf.2 hq⟩, inv_mul_cancel_right _ _⟩

end GlobalTheory.SphEis
