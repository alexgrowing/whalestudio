import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
open Matrix

noncomputable section
namespace GlobalTheory.SvNAnyChar

def scaleSnd {k : Type} [Field k] {κ : Type} (c : k) :
    (κ → k) × (κ → k) →+ (κ → k) × (κ → k) where
  toFun w := (w.1, c • w.2)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem scaleSnd_fst {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).1 = w.1 := rfl

@[simp] theorem scaleSnd_snd {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).2 = c • w.2 := rfl

theorem schr_mulShift_scaleSnd {k : Type} [Field k] [Invertible (2 : k)] {κ : Type} [Fintype κ]
    (ψ : AddChar k ℂ) {c : k} (hc : c ≠ 0) (w : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    GlobalTheory.WeilM.schr (ψ.mulShift c) (scaleSnd c⁻¹ w) φ = GlobalTheory.WeilM.schr ψ w φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, scaleSnd_fst, scaleSnd_snd, AddChar.mulShift_apply, dotProduct_smul,
    smul_eq_mul]
  congr 2
  rw [mul_add, mul_left_comm c (⅟2), mul_inv_cancel_left₀ hc, mul_inv_cancel_left₀ hc]

theorem stoneVonNeumann_any_char :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc, hcond⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  have hψ1 : Continuous (ψ0.mulShift c) := by
    have : (ψ0.mulShift c : k → ℂ) = fun x => ψ0 (c * x) := by
      funext x
      exact AddChar.mulShift_apply
    rw [this]
    exact hψ.comp (continuous_const.mul continuous_id)
  let S : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k :=
    { toFun := fun z => c • z
      map_zero' := smul_zero c
      map_add' := smul_add c }
  have hS : ∀ z, S z = c • z := fun _ => rfl
  have hsum : ∀ (a : k) (Y z : Matrix (Fin n) (Fin d) k),
      ∑ i, ∑ j, Y i j * (a • z) i j = a * ∑ i, ∑ j, Y i j * z i j := by
    intro a Y z
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι, hbij, h1, h2⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (κ := κ) (n := n) (d := d) (ψ0.mulShift c) hψ1
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x)
    ((scaleSnd c⁻¹).comp wT) ((scaleSnd c⁻¹).comp (wM.comp S))
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hT, mul_zero])
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hM, mul_zero])
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hTM, hS, hsum, inv_mul_cancel_left₀ hc])
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (scaleSnd c w)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      simp only [AddMonoidHom.comp_apply]
      rw [hS, smul_inv_smul₀ hc, ← map_add, h]
      exact Prod.ext rfl (inv_smul_smul₀ hc _))
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · have := h1 Y φ hφ
    rwa [AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc] at this
  · have := h2 (c⁻¹ • z) φ hφ
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc, hS,
      smul_inv_smul₀ hc] at this
    rw [this]
    funext Y'
    rw [AddChar.mulShift_apply, hsum, mul_inv_cancel_left₀ hc]

end GlobalTheory.SvNAnyChar
