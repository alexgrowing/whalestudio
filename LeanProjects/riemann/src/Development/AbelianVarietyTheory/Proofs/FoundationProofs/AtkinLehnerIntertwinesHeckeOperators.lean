import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehner

def alQ (N l : ℕ) (a b c d : ℤ) : M2 := !![(N : ℤ) * a, b; N * l * c, N * d]

def alConj (N l : ℕ) (a b c d : ℤ) (M : M2) : M2 :=
  !![N*a*d*M 0 0 - N*l*a*b*(M 1 0 / ((N : ℤ) * l)) + N*l*c*d*M 0 1 - l*b*c*M 1 1,
     b*d*M 0 0 - l*b^2*(M 1 0 / ((N : ℤ) * l)) + N*d^2*M 0 1 - b*d*M 1 1;
     N*l*(-a*c*M 0 0 + N*a^2*(M 1 0 / ((N : ℤ) * l)) - l*c^2*M 0 1 + a*c*M 1 1),
     -l*b*c*M 0 0 + N*l*a*b*(M 1 0 / ((N : ℤ) * l)) - N*l*c*d*M 0 1 + N*a*d*M 1 1]

def alConjInv (N l : ℕ) (a b c d : ℤ) (M : M2) : M2 :=
  !![N*a*d*M 0 0 + N*l*b*d*(M 1 0 / ((N : ℤ) * l)) - N*l*a*c*M 0 1 - l*b*c*M 1 1,
     -a*b*M 0 0 - l*b^2*(M 1 0 / ((N : ℤ) * l)) + N*a^2*M 0 1 + a*b*M 1 1;
     N*l*(c*d*M 0 0 + N*d^2*(M 1 0 / ((N : ℤ) * l)) - l*c^2*M 0 1 - c*d*M 1 1),
     -l*b*c*M 0 0 - N*l*b*d*(M 1 0 / ((N : ℤ) * l)) + N*l*a*c*M 0 1 + N*a*d*M 1 1]

section
variable {N l : ℕ} {a b c d : ℤ}

theorem mul_alConj (h : (N : ℤ) * a * d - l * b * c = 1) (hNl : (N : ℤ) * l ≠ 0) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : alQ N l a b c d * alConj N l a b c d M = M * alQ N l a b c d := by
  obtain ⟨z, hz⟩ := hM
  push_cast at hz
  have hz' : M 1 0 / ((N : ℤ) * l) = z := by rw [hz]; exact Int.mul_ediv_cancel_left z hNl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [alQ, alConj, Matrix.mul_apply, Fin.sum_univ_two, hz', Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try rw [hz])
  · linear_combination ((N : ℤ) * a * M 0 0 + N * l * c * M 0 1) * h
  · linear_combination (b * M 0 0 + N * d * M 0 1) * h
  · linear_combination ((N : ℤ) * l * z * (N * a) + M 1 1 * (N * l * c)) * h
  · linear_combination ((N : ℤ) * l * z * b + M 1 1 * (N * d)) * h

theorem alConjInv_mul (h : (N : ℤ) * a * d - l * b * c = 1) (hNl : (N : ℤ) * l ≠ 0) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : alConjInv N l a b c d M * alQ N l a b c d = alQ N l a b c d * M := by
  obtain ⟨z, hz⟩ := hM
  push_cast at hz
  have hz' : M 1 0 / ((N : ℤ) * l) = z := by rw [hz]; exact Int.mul_ediv_cancel_left z hNl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [alQ, alConjInv, Matrix.mul_apply, Fin.sum_univ_two, hz', Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try rw [hz])
  · linear_combination ((N : ℤ) * a * M 0 0 + b * (N * l * z)) * h
  · linear_combination ((N : ℤ) * a * M 0 1 + b * M 1 1) * h
  · linear_combination ((N : ℤ) * l * c * M 0 0 + N * d * (N * l * z)) * h
  · linear_combination ((N : ℤ) * l * c * M 0 1 + N * d * M 1 1) * h

theorem alQ_det (h : (N : ℤ) * a * d - l * b * c = 1) : (alQ N l a b c d).det = N := by
  simp only [alQ, Matrix.det_fin_two_of]
  linear_combination (N : ℤ) * h

end

section
variable {N l : ℕ} {a b c d : ℤ}

theorem alQ_cancel_left (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) {A B : M2}
    (hAB : alQ N l a b c d * A = alQ N l a b c d * B) : A = B := by
  have e := congrArg (fun X => (alQ N l a b c d).adjugate * X) hAB
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, alQ_det h, Matrix.smul_mul, one_mul] at e
  exact smul_right_injective M2 (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) e

theorem alQ_cancel_right (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) {A B : M2}
    (hAB : A * alQ N l a b c d = B * alQ N l a b c d) : A = B := by
  have e := congrArg (fun X => X * (alQ N l a b c d).adjugate) hAB
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, alQ_det h, Matrix.mul_smul, mul_one] at e
  exact smul_right_injective M2 (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) e

theorem alConj_mem (M : M2) : ((N * l : ℕ) : ℤ) ∣ alConj N l a b c d M 1 0 := by
  simp only [alConj, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  exact Dvd.intro _ rfl

theorem alConjInv_mem (M : M2) : ((N * l : ℕ) : ℤ) ∣ alConjInv N l a b c d M 1 0 := by
  simp only [alConjInv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  exact Dvd.intro _ rfl

theorem mul_mem {L : ℕ} {A B : M2} (hA : (L : ℤ) ∣ A 1 0) (hB : (L : ℤ) ∣ B 1 0) : (L : ℤ) ∣ (A * B) 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_right hB _)

theorem alConj_det (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : (alConj N l a b c d M).det = M.det := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  have e := congrArg Matrix.det (mul_alConj h hNl M hM)
  rw [Matrix.det_mul, Matrix.det_mul, alQ_det h, mul_comm M.det] at e
  exact mul_left_cancel₀ (by exact_mod_cast hN.ne') e

theorem alConjInv_det (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : (alConjInv N l a b c d M).det = M.det := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  have e := congrArg Matrix.det (alConjInv_mul h hNl M hM)
  rw [Matrix.det_mul, Matrix.det_mul, alQ_det h, mul_comm] at e
  exact mul_left_cancel₀ (by exact_mod_cast hN.ne') e

theorem alConj_alConjInv (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : alConj N l a b c d (alConjInv N l a b c d M) = M := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  apply alQ_cancel_left h hN
  rw [mul_alConj h hNl _ (alConjInv_mem M), alConjInv_mul h hNl M hM]

theorem alConjInv_alConj (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (M : M2)
    (hM : ((N * l : ℕ) : ℤ) ∣ M 1 0) : alConjInv N l a b c d (alConj N l a b c d M) = M := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  apply alQ_cancel_right h hN
  rw [alConjInv_mul h hNl _ (alConj_mem M), mul_alConj h hNl M hM]

theorem alConj_mul (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (A B : M2)
    (hA : ((N * l : ℕ) : ℤ) ∣ A 1 0) (hB : ((N * l : ℕ) : ℤ) ∣ B 1 0) :
    alConj N l a b c d (A * B) = alConj N l a b c d A * alConj N l a b c d B := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  apply alQ_cancel_left h hN
  calc alQ N l a b c d * alConj N l a b c d (A * B) = A * B * alQ N l a b c d := mul_alConj h hNl _ (mul_mem hA hB)
    _ = A * (alQ N l a b c d * alConj N l a b c d B) := by rw [Matrix.mul_assoc, mul_alConj h hNl B hB]
    _ = alQ N l a b c d * alConj N l a b c d A * alConj N l a b c d B := by
        rw [← Matrix.mul_assoc, mul_alConj h hNl A hA]
    _ = _ := Matrix.mul_assoc _ _ _

theorem alConjInv_mul' (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (A B : M2)
    (hA : ((N * l : ℕ) : ℤ) ∣ A 1 0) (hB : ((N * l : ℕ) : ℤ) ∣ B 1 0) :
    alConjInv N l a b c d (A * B) = alConjInv N l a b c d A * alConjInv N l a b c d B := by
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  apply alQ_cancel_right h hN
  calc alConjInv N l a b c d (A * B) * alQ N l a b c d = alQ N l a b c d * (A * B) := alConjInv_mul h hNl _ (mul_mem hA hB)
    _ = alConjInv N l a b c d A * alQ N l a b c d * B := by rw [alConjInv_mul h hNl A hA, Matrix.mul_assoc]
    _ = alConjInv N l a b c d A * (alConjInv N l a b c d B * alQ N l a b c d) := by
        rw [alConjInv_mul h hNl B hB, Matrix.mul_assoc]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

theorem alConj_00_N (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (M : M2) :
    (N : ℤ) ∣ alConj N l a b c d M 0 0 - M 1 1 := by
  simp only [alConj, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  exact ⟨a * d * M 0 0 - l * a * b * (M 1 0 / ((N : ℤ) * l)) + l * c * d * M 0 1 - a * d * M 1 1,
    by linear_combination (M 1 1) * h⟩

theorem alConj_00_l (h : (N : ℤ) * a * d - l * b * c = 1) (M : M2) :
    (l : ℤ) ∣ alConj N l a b c d M 0 0 - M 0 0 := by
  simp only [alConj, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  exact ⟨b * c * M 0 0 - N * a * b * (M 1 0 / ((N : ℤ) * l)) + N * c * d * M 0 1 - b * c * M 1 1,
    by linear_combination (M 0 0) * h⟩

theorem alConjInv_00_l (h : (N : ℤ) * a * d - l * b * c = 1) (M : M2) :
    (l : ℤ) ∣ alConjInv N l a b c d M 0 0 - M 0 0 := by
  simp only [alConjInv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  exact ⟨b * c * M 0 0 + N * b * d * (M 1 0 / ((N : ℤ) * l)) - N * a * c * M 0 1 - b * c * M 1 1,
    by linear_combination (M 0 0) * h⟩

end

def toG0 (L : ℕ) (M : M2) (h1 : M.det = 1) (h2 : (L : ℤ) ∣ M 1 0) : Gamma0 L :=
  ⟨⟨M, h1⟩, Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2)⟩

theorem coe_to_gamma0 (L : ℕ) (M : M2) (h1 : M.det = 1) (h2 : (L : ℤ) ∣ M 1 0) :
    (((toG0 L M h1 h2 : Gamma0 L) : SL(2, ℤ)) : M2) = M := rfl

theorem gamma0_lowerLeft_dvd_level {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

section
variable {N l : ℕ} {a b c d : ℤ}

theorem lrep_alConj (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l) (Δ : Set M2)
    (hΔ : ∀ δ ∈ Δ, ((N * l : ℕ) : ℤ) ∣ δ 1 0) (hφ : ∀ δ ∈ Δ, alConj N l a b c d δ ∈ Δ)
    (hψ : ∀ δ ∈ Δ, alConjInv N l a b c d δ ∈ Δ) {ι : Type} (β : ι → M2) (hβ : LRep (N * l) Δ β) :
    LRep (N * l) Δ (fun i => alConj N l a b c d (β i)) := by
  have hG : ∀ γ : Gamma0 (N * l), ((N * l : ℕ) : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := fun γ => gamma0_lowerLeft_dvd_level γ
  have hGdet : ∀ γ : Gamma0 (N * l), ((γ : SL(2, ℤ)) : M2).det = 1 := fun γ => (γ : SL(2, ℤ)).2
  let ψG : Gamma0 (N * l) → Gamma0 (N * l) := fun γ => toG0 (N * l) (alConjInv N l a b c d ((γ : SL(2, ℤ)) : M2))
    (by rw [alConjInv_det h hN hl _ (hG γ), hGdet]) (alConjInv_mem _)
  let φG : Gamma0 (N * l) → Gamma0 (N * l) := fun γ => toG0 (N * l) (alConj N l a b c d ((γ : SL(2, ℤ)) : M2))
    (by rw [alConj_det h hN hl _ (hG γ), hGdet]) (alConj_mem _)
  have hβΔ : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 (N * l)), i))
    simpa using this
  have e1 : ∀ (γ : Gamma0 (N * l)) i, alConjInv N l a b c d (((γ : SL(2, ℤ)) : M2) * alConj N l a b c d (β i))
      = (((ψG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) * β i := by
    intro γ i
    rw [alConjInv_mul' h hN hl _ _ (hG γ) (alConj_mem _), alConjInv_alConj h hN hl _ (hΔ _ (hβΔ i))]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    show ((γ : SL(2, ℤ)) : M2) * alConj N l a b c d (β i) ∈ Δ
    have e : ((γ : SL(2, ℤ)) : M2) * alConj N l a b c d (β i)
        = alConj N l a b c d ((((ψG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) * β i) := by
      rw [show (((ψG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) = alConjInv N l a b c d ((γ : SL(2, ℤ)) : M2) from rfl,
        alConj_mul h hN hl _ _ (alConjInv_mem _) (hΔ _ (hβΔ i)), alConj_alConjInv h hN hl _ (hG γ)]
    rw [e]
    exact hφ _ (hβ.mapsTo (Set.mem_univ (ψG γ, i)))
  · rintro ⟨γ, i⟩ - ⟨γ', j⟩ - hE
    simp only at hE
    have := hβ.injOn (Set.mem_univ (ψG γ, i)) (Set.mem_univ (ψG γ', j)) (by
      show (((ψG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) * β i = (((ψG γ' : Gamma0 (N * l)) : SL(2, ℤ)) : M2) * β j
      rw [← e1, ← e1, hE])
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, rfl⟩ := this
    have h2 : ((γ : SL(2, ℤ)) : M2) = ((γ' : SL(2, ℤ)) : M2) := by
      have h3 := congrArg (fun g : Gamma0 (N * l) => alConj N l a b c d ((g : SL(2, ℤ)) : M2)) h1
      simp only [ψG, coe_to_gamma0] at h3
      rwa [alConj_alConjInv h hN hl _ (hG γ), alConj_alConjInv h hN hl _ (hG γ')] at h3
    have : γ = γ' := Subtype.ext (Subtype.ext h2)
    rw [this]
  · intro δ hδ
    obtain ⟨⟨γ, i⟩, -, hγ⟩ := hβ.surjOn (hψ δ hδ)
    simp only at hγ
    refine ⟨(φG γ, i), Set.mem_univ _, ?_⟩
    show (((φG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) * alConj N l a b c d (β i) = δ
    rw [show (((φG γ : Gamma0 (N * l)) : SL(2, ℤ)) : M2) = alConj N l a b c d ((γ : SL(2, ℤ)) : M2) from rfl,
      ← alConj_mul h hN hl _ _ (hG γ) (hΔ _ (hβΔ i)), hγ, alConj_alConjInv h hN hl _ (hΔ _ hδ)]

theorem weight_alConj (χ : DirichletCharacter ℂ N) (h : (N : ℤ) * a * d - l * b * c = 1) (hN : 0 < N) (hl : 0 < l)
    (m : ℕ) (hm : m.Coprime N) (δ : M2) (hdet : δ.det = m) (hδ : ((N * l : ℕ) : ℤ) ∣ δ 1 0) :
    ch χ (δ 0 0) = ch χ m * ch χ⁻¹ (alConj N l a b c d δ 0 0) := by
  have hN10 : (N : ℤ) ∣ δ 1 0 := dvd_trans ⟨l, by push_cast; ring⟩ hδ
  have e1 : ((alConj N l a b c d δ 0 0 : ℤ) : ZMod N) = ((δ 1 1 : ℤ) : ZMod N) :=
    ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (alConj_00_N h hN hl δ)).symm
  have e2 : ((δ 0 0 : ℤ) : ZMod N) * ((δ 1 1 : ℤ) : ZMod N) = (m : ZMod N) := by
    have e3 : ((δ.det : ℤ) : ZMod N) = (m : ZMod N) := by rw [hdet]; simp
    rw [Matrix.det_fin_two] at e3
    push_cast at e3
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hN10, mul_zero, sub_zero] at e3
    exact e3
  have hu : IsUnit (m : ZMod N) := (ZMod.unitOfCoprime m hm).isUnit
  have hv : IsUnit ((δ 1 1 : ℤ) : ZMod N) := isUnit_of_mul_isUnit_right (e2 ▸ hu)
  have hχv : χ ((δ 1 1 : ℤ) : ZMod N) ≠ 0 := (hv.map χ).ne_zero
  simp only [ch]
  rw [e1, MulChar.inv_apply_eq_inv', Int.cast_natCast, ← e2, map_mul]
  field_simp

theorem slz_fsum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (w : ι → ℂ) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i, w i * g i σ) τ = ∑ i, w i * slz k δ (g i) τ := by
  simp only [slz, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem slz_alQ_hsum (k : ℕ) (χ : DirichletCharacter ℂ N) (h : (N : ℤ) * a * d - l * b * c = 1) (hk : 1 ≤ k)
    (hN : 0 < N) (hl : 0 < l) (Δ : Set M2) (m : ℕ) (hm0 : 0 < m) (hm : m.Coprime N)
    (hΔ : ∀ δ ∈ Δ, δ.det = m ∧ ((N * l : ℕ) : ℤ) ∣ δ 1 0) (hφ : ∀ δ ∈ Δ, alConj N l a b c d δ ∈ Δ)
    (hψ : ∀ δ ∈ Δ, alConjInv N l a b c d δ ∈ Δ) {ι : Type} [Fintype ι] (β : ι → M2) (hβ : LRep (N * l) Δ β)
    (f f' : ℍ → ℂ) (hf' : f' = slz k (alQ N l a b c d) f) (hinv : Inv k (N * l) (ch χ⁻¹) f') :
    slz k (alQ N l a b c d) (hsum k (ch χ) β f) = ch χ m • hsum k (ch χ⁻¹) β f' := by
  obtain ⟨hmul, -⟩ := slz_props k f hk
  have hNl : (N : ℤ) * l ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hl.ne')
  have hQ : 0 < (alQ N l a b c d).det := by rw [alQ_det h]; exact_mod_cast hN
  have hβΔ : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 (N * l)), i))
    simpa using this
  have hβd : ∀ i, 0 < (β i).det := fun i => by rw [(hΔ _ (hβΔ i)).1]; exact_mod_cast hm0
  have hφβ := lrep_alConj h hN hl Δ (fun δ hδ => (hΔ δ hδ).2) hφ hψ β hβ
  have hind := RepInd.hsum_indep k (N * l) N χ⁻¹ Δ ι ι _ β f' hk (dvd_mul_right N l)
    (fun δ hδ => ⟨by rw [(hΔ δ hδ).1]; exact_mod_cast hm0,
      dvd_trans ⟨l, by push_cast; ring⟩ (hΔ δ hδ).2⟩) hφβ hβ hinv
  rw [← hind]
  funext τ
  have hterm : ∀ i, slz k (alQ N l a b c d) (slz k (β i) f) = slz k (alConj N l a b c d (β i)) f' := by
    intro i
    rw [← hmul _ _ (hβd i) hQ, ← mul_alConj h hNl _ (hΔ _ (hβΔ i)).2,
      hmul _ _ hQ (by rw [alConj_det h hN hl _ (hΔ _ (hβΔ i)).2]; exact hβd i), hf']
  rw [show hsum k (ch χ) β f = fun σ => ∑ i, ch χ (β i 0 0) * slz k (β i) f σ from rfl, slz_fsum]
  simp only [Pi.smul_apply, smul_eq_mul, hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i, weight_alConj χ h hN hl m hm (β i) (hΔ _ (hβΔ i)).1 (hΔ _ (hβΔ i)).2]
  ring

end

theorem alHecke : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a a' : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (To k (ch χ q) q a)) = (ch χ q : ℂ) • qs (To k (ch χ⁻¹ q) q a')) ∧ slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (Uo l a)) = (ch χ l : ℂ) • qs (Uo l a') := by
  intro k N l χ a a' a₀ b₀ c₀ d₀ h hk hN hl hlN ha ha' hqs
  have hl0 : 0 < l := hl.pos
  have hQ : !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] = alQ N l a₀ b₀ c₀ d₀ := rfl
  rw [hQ] at hqs ⊢
  have hinv : Inv k (N * l) (ch χ⁻¹) (qs a') := ha'.2
  have hφT : ∀ q : ℕ, ∀ δ ∈ DT (N * l) q, alConj N l a₀ b₀ c₀ d₀ δ ∈ DT (N * l) q := fun q δ hδ =>
    ⟨by rw [alConj_det h hN hl0 δ hδ.2]; exact hδ.1, alConj_mem δ⟩
  have hψT : ∀ q : ℕ, ∀ δ ∈ DT (N * l) q, alConjInv N l a₀ b₀ c₀ d₀ δ ∈ DT (N * l) q := fun q δ hδ =>
    ⟨by rw [alConjInv_det h hN hl0 δ hδ.2]; exact hδ.1, alConjInv_mem δ⟩
  constructor
  · intro q hq hqNl
    have hqN : ¬ q ∣ N := fun hd => hqNl (dvd_mul_of_dvd_left hd l)
    have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
    rw [(qs_To_hsum k q (ch χ) a hk hq.pos (by simp [ch]) ha.1).2,
      (qs_To_hsum k q (ch χ⁻¹) a' hk hq.pos (by simp [ch]) ha'.1).2]
    exact slz_alQ_hsum k χ h hk hN hl0 (DT (N * l) q) q hq.pos hcop (fun δ hδ => ⟨hδ.1, hδ.2⟩) (hφT q) (hψT q)
      (repT q) (lRep_DT_repT (N * l) q hq hqNl) (qs a) (qs a') hqs hinv
  · have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
    have hU : ∀ (ε : DirichletCharacter ℂ N) (b : ℕ → ℂ), PolyB b → qs (Uo l b) = hsum k (ch ε) (repU l) (qs b) := by
      intro ε b hb
      funext τ
      rw [(Uo_qs_sum_slz k l b hk hl0 hb).2 τ]
      simp [hsum, repU, ch]
    rw [hU χ a ha.1, hU χ⁻¹ a' ha'.1]
    have hφU : ∀ δ ∈ DU (N * l) l, alConj N l a₀ b₀ c₀ d₀ δ ∈ DU (N * l) l := fun δ hδ =>
      ⟨by rw [alConj_det h hN hl0 δ hδ.2.1]; exact hδ.1, alConj_mem δ, fun hd => hδ.2.2 (by
        have := dvd_sub hd (alConj_00_l h δ); simpa using this)⟩
    have hψU : ∀ δ ∈ DU (N * l) l, alConjInv N l a₀ b₀ c₀ d₀ δ ∈ DU (N * l) l := fun δ hδ =>
      ⟨by rw [alConjInv_det h hN hl0 δ hδ.2.1]; exact hδ.1, alConjInv_mem δ, fun hd => hδ.2.2 (by
        have := dvd_sub hd (alConjInv_00_l h δ); simpa using this)⟩
    exact slz_alQ_hsum k χ h hk hN hl0 (DU (N * l) l) l hl0 hcop (fun δ hδ => ⟨hδ.1, hδ.2.1⟩) hφU hψU
      (repU l) ((zrepU (N * l) l hl).1 (dvd_mul_left l N)) (qs a) (qs a') hqs hinv

end GlobalTheory.EisM.AtkinLehner
