import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResidueEisenstein.FrameLeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem absE_det_of_scalesBy {k : ℕ} {X : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * X = 1)
    {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X γ β) :
    absE F E (Matrix.GeneralLinearGroup.det β) = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F X = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : β.1 = (L * γ0.1.1 * X).map (inclR (F := F) (AF F)) := by
    have := congrArg (adMat F L * ·) e
    have h2 : adMat F L * (adMat F X * β.1) = β.1 := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    rw [h2, hmat] at this
    rw [← this]
    simp only [adMat, Matrix.map_mul, Matrix.mul_assoc]
  set c : E := (L * γ0.1.1 * X).det with hc
  have hd : (Matrix.GeneralLinearGroup.det β).1 = inclR (F := F) (AF F) c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb, hc, RingHom.map_det]
    rfl
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := (Matrix.GeneralLinearGroup.det β).mul_inv
      rw [hd, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim (Matrix.GeneralLinearGroup.det β) 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = Matrix.GeneralLinearGroup.det β from
      Units.ext (by simp [hd])] at this

end GlobalTheory.ResidueEisenstein.FrameLeviFacts

namespace GlobalTheory.ResidueEisenstein

open GlobalTheory.StdPar GlobalTheory.ResLine.LeviFacts in

theorem frame_levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hX : initCols X (Fin.last r) = X := rfl
  have hY : initCols Y (Fin.last r) = Y := rfl
  have hlev : ∀ m ∈ levi σ J X Y {Fin.last r}, m ∈ frameStab σ J X ⊤ ∧ m ∈ frameStab σ J Y ⊤ := fun m hm => by
    simp only [levi, Subgroup.mem_iInf] at hm
    exact hm _ (Finset.mem_singleton_self _)
  refine ⟨fun m hm u hu => conj_mem hW (Fin.last r) (hlev m hm).1 hu,
    fun g hg hm => eq_one h hJ hW (Fin.last r) hg (hlev g hm).2,
    fun u hu => (unipRad_fix hu).trans (by simp), fun m hm => ?_,
    fun γ hγ β e => FrameLeviFacts.absE_det_of_scalesBy (yx h hJ hW) hγ e, inf_le_left,
    (isClosed_levi {Fin.last r} h hJ hW).2⟩
  have h2 : m ∈ ⨅ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
  simp only [Subgroup.mem_iInf] at h2
  obtain ⟨B, hB, e⟩ := h2 _ (Finset.mem_singleton_self _)
  exact ⟨B, e, hB⟩

end GlobalTheory.ResidueEisenstein
end
