import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtEx

theorem continuous_of_decomp {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace X]
    {Q : Subgroup Γ} (hQ : IsClosed (Q : Set Γ)) {C : Set Γ} (hC : IsCompact C) (H : Γ → X) (δ : Q → X)
    (hδ : Continuous δ) (hI : ∀ g, ∃ p ∈ Q, ∃ k ∈ C, g = p * k)
    (hH : ∀ (p : Q), ∀ k ∈ C, H ((p : Γ) * k) = δ p) : Continuous H := by
  rw [continuous_iff_isClosed]
  intro F hF
  have hQF : IsClosed ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) :=
    hQ.isClosedMap_subtype_val _ (hF.preimage hδ)
  have heq : H ⁻¹' F = Set.image2 (· * ·) ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) C := by
    ext g
    constructor
    · intro hg
      obtain ⟨p, hp, k, hk, rfl⟩ := hI g
      refine Set.mem_image2.mpr ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      have h1 := hH ⟨p, hp⟩ k hk
      simp only [Set.mem_preimage] at hg ⊢
      rw [← h1]
      exact hg
    · intro hg
      obtain ⟨x, ⟨q, hq, rfl⟩, k, hk, rfl⟩ := Set.mem_image2.mp hg
      simp only [Set.mem_preimage] at hq ⊢
      rw [hH q k hk]
      exact hq
  rw [heq]
  exact hQF.mul_right_of_isCompact hC

variable {D : D7} {n : ℕ}

def delta : P D n →* ℝ≥0 :=
  (absA D).comp (Matrix.GeneralLinearGroup.det.comp HeightExists.leviBlock)

theorem continuous_delta : Continuous (delta (D := D) (n := n)) := by
  have hA : Continuous (absA D) := GlobalTheory.Doubling.continuous_absE
  exact hA.comp (HeightExists.continuous_detGL.comp HeightExists.continuous_leviBlock)

theorem absA_pos (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem delta_eq {p : G D n} (hp : p ∈ P D n) {a : GL (Fin n) (AE D)} (ha : blkA (mat p) = a.1) :
    delta (⟨p, hp⟩ : P D n) = absA D (Matrix.GeneralLinearGroup.det a) := by
  have hl : HeightExists.leviBlock (⟨p, hp⟩ : P D n) = a := by
    ext1
    exact ha
  show absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (⟨p, hp⟩ : P D n))) = _
  rw [hl]

theorem height_eq {H : G D n → ℝ≥0} (hH : IsHeight H) (p : P D n) {k : G D n} (hk : k ∈ K D n) :
    H ((p : G D n) * k) = delta p := by
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA p.2
  rw [hH p p.2 a ha k hk, ← delta_eq p.2 ha]

theorem isHt_of_isHeight {H : G D n → ℝ≥0} (hH : IsHeight H) : PositivityTheory.Rg.Rsw.IsHt H := by
  refine ⟨continuous_of_decomp HeightExists.isClosed_P HeightExists.isCompact_K H delta continuous_delta
    (Iwasawa.exists_mul D n) (fun p k hk => height_eq hH p hk), ?_, ?_⟩
  · intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [height_eq hH ⟨p, hp⟩ hk]
    obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
    rw [delta_eq hp ha]
    exact absA_pos _
  · intro q hq a ha g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [← mul_assoc, height_eq hH ⟨q * p, (P D n).mul_mem hq hp⟩ hk, height_eq hH ⟨p, hp⟩ hk,
      ← delta_eq hq ha]
    exact map_mul delta (⟨q, hq⟩ : P D n) ⟨p, hp⟩

theorem htExist : PositivityTheory.Rg.Rsw.HtExist := by
  intro D n
  refine ⟨?_, (K D n : Set (G D n)), HeightExists.isCompact_K, fun g => ?_⟩
  · obtain ⟨H, hH⟩ := exists_height D n
    exact ⟨H, isHt_of_isHeight hH⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    exact ⟨p, hp, k, hk, rfl⟩

end GlobalTheory.CompanionTheory.HtEx

end
