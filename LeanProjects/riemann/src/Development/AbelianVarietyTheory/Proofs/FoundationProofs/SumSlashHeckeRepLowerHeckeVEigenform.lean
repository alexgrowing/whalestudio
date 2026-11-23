import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepRepsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem slz_const_mul (k : ℕ) (δ : M2) (c : ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => c * g σ) τ = c * slz k δ g τ := by
  unfold slz; ring

private theorem slz_sub (k : ℕ) (δ : M2) (g g' : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => g σ - g' σ) τ = slz k δ g τ - slz k δ g' τ := by
  unfold slz; ring

private theorem slz_sum {ι : Type} (s : Finset ι) (k : ℕ) (δ : M2) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i ∈ s, g i σ) τ = ∑ i ∈ s, slz k δ (g i) τ := by
  unfold slz; rw [Finset.mul_sum]

theorem qs_Vo_slz (k l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    qs (Vo l a) τ = ((l : ℂ) ^ (k - 1))⁻¹ * slz k !![(l : ℤ), 0; 0, 1] (qs a) τ := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have him : 0 < ((l : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hl) τ.im_pos
  have hV := (GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl ha).2 τ ⟨(l : ℂ) * τ, him⟩ rfl
  rw [hV]
  unfold slz
  simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  simp only [zero_mul, zero_add, mul_one, mul_zero, sub_zero, add_zero, div_one, one_pow, inv_one]
  rw [ofComplex_apply_of_im_pos him]
  field_simp

end GlobalTheory.EisM

namespace GlobalTheory.EisM

private theorem qs_smul (t : ℂ) (a : ℕ → ℂ) : qs (t • a) = fun τ => t * qs a τ := by
  funext τ; unfold qs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem sum_slz_repL_Vo : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  intro k N l ε h t hk hN hl hlN hMF hT τ
  have hl0 : 0 < l := hl.pos
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  set F := qs h with hF
  set D : M2 := !![(l : ℤ), 0; 0, 1] with hD
  set E : M2 := !![(1 : ℤ), 0; 0, (l : ℤ)] with hE
  have hcoc := GlobalTheory.T.slashIntMatrixPosDet_properties k

  have hTq := (GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k l (ch ε) h hk hl0 (by simp [ch]) hMF.1).2
  rw [hT, qs_smul] at hTq
  have hind := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k N N ε (DT N l) (Option (Fin l)) (Option (Fin l)) (repT l) (repL N l) F hk dvd_rfl
    (fun δ hδ => ⟨by rw [hδ.1]; exact_mod_cast hl0, hδ.2⟩) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator N l hl hlN) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel N l hl hlN) hMF.2
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hu : IsUnit (((l : ℤ) : ZMod N)) := by
    rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime l N).2 hcop
  have hεl : ch ε l ≠ 0 := by
    unfold ch; exact (IsUnit.map ε hu).ne_zero
  have hinv : ch ε⁻¹ l = (ch ε l)⁻¹ := by
    unfold ch; rw [MulChar.inv_apply_eq_inv']
  have key : ∀ σ : ℍ, ∑ j : Fin l, slz k (repL N l (some j)) F σ = (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    intro σ
    have h1 := congrFun hTq σ
    rw [hind] at h1
    unfold hsum at h1
    rw [Fintype.sum_option] at h1
    have h2 : repL N l none = E := rfl
    rw [h2] at h1
    have h3 : ∀ j : Fin l, ch ε (repL N l (some j) 0 0) = ch ε l := by
      intro j; simp [repL]
    have h4 : ch ε (E 0 0) = 1 := by simp [hE, ch]
    simp only [h3, h4, one_mul, ← Finset.mul_sum] at h1
    field_simp
    rw [← hF] at h1
    linear_combination -h1
  have hVfun : qs (Vo l h) = fun σ => ((l : ℂ) ^ (k - 1))⁻¹ * slz k D F σ := by
    funext σ; exact qs_Vo_slz k l hl0 h hMF.1 σ
  have hdetD : 0 < D.det := by simp [hD, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetE : 0 < E.det := by simp [hE, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetA : ∀ (L : ℕ) (j : Fin l), 0 < (repL L l (some j)).det := by
    intro L j; simp [repL, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hmat : ∀ j : Fin l, D * repL (N * l) l (some j) = repL N l (some j) * D := by
    intro j
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring
  have hED : E * D = !![((l : ℕ) : ℤ), 0; 0, ((l : ℕ) : ℤ)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ =
      ((l : ℂ) ^ (k - 1))⁻¹ * slz k D (slz k (repL N l (some j)) F) τ := by
    intro j
    rw [hVfun, slz_const_mul]
    congr 1
    rw [← (hcoc F hk).1 D _ hdetD (hdetA _ j), hmat j, (hcoc F hk).1 _ D (hdetA _ j) hdetD]
  simp only [hterm]
  rw [← Finset.mul_sum, ← slz_sum]
  have hfun : (fun σ => ∑ j : Fin l, slz k (repL N l (some j)) F σ) = fun σ => (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    funext σ; exact key σ
  rw [hfun, slz_const_mul, slz_sub, slz_const_mul]
  have hDE : slz k D (slz k E F) τ = (l : ℂ) ^ k / (l : ℂ) ^ 2 * F τ := by
    rw [← (hcoc F hk).1 E D hdetE hdetD, hED]
    exact (hcoc F hk).2.2.2.2 l τ hl0
  rw [hDE, hinv]
  have hV := qs_Vo_slz k l hl0 h hMF.1 τ
  rw [hV]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end GlobalTheory.EisM
