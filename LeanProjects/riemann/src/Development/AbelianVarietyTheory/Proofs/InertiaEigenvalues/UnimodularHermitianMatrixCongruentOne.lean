import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormOneAddEqOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.HermUnimod

section Gen

variable {E : Type} [NormedField E]

def Intg {n m : Type} (h : Matrix n m E) : Prop := ∀ i j, ‖h i j‖ ≤ 1

theorem nsum_le [IsUltrametricDist E] {ι : Type} (s : Finset ι) (f : ι → E) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, ‖f i‖ ≤ r) :
    ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem intg_mul [IsUltrametricDist E] {l n m : Type} [Fintype n] {A : Matrix l n E} {B : Matrix n m E} (hA : Intg A)
    (hB : Intg B) : Intg (A * B) := by
  intro i j
  rw [mul_apply]
  refine nsum_le _ _ zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem intg_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n m : Type} {A : Matrix n m E} (hA : Intg A) :
    Intg Aᴴ := by
  intro i j
  rw [conjTranspose_apply, hs]
  exact hA j i

theorem intg_one {n : Type} [DecidableEq n] : Intg (1 : Matrix n n E) := by
  intro i j
  rw [one_apply]
  split_ifs <;> simp

theorem norm_det_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n E) : ‖Aᴴ.det‖ = ‖A.det‖ := by
  rw [det_conjTranspose, hs]

def Good (n : Type) [Fintype n] [DecidableEq n] (E : Type) [NormedField E] [StarRing E] : Prop :=
  ∀ G : Matrix n n E, G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1

end Gen

section Step

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem intg_fromBlocks {l m n o : Type} {A : Matrix n l E} {B : Matrix n m E} {C : Matrix o l E}
    {D : Matrix o m E} (hA : Intg A) (hB : Intg B) (hC : Intg C) (hD : Intg D) :
    Intg (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem intg_sub {n m : Type} {A B : Matrix n m E} (hA : Intg A) (hB : Intg B) : Intg (A - B) := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (by rw [norm_neg]; exact hB i j))

theorem intg_neg {n m : Type} {A : Matrix n m E} (hA : Intg A) : Intg (-A) := by
  intro i j
  rw [neg_apply, norm_neg]
  exact hA i j

theorem intg_zero {n m : Type} : Intg (0 : Matrix n m E) := by
  intro i j
  simp

theorem schur_conj {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E) (B : Matrix m Unit E) :
    (fromBlocks 1 0 (-Bᴴ) 1 : Matrix (m ⊕ Unit) (m ⊕ Unit) E)ᴴ * fromBlocks A B Bᴴ 1 *
        fromBlocks 1 0 (-Bᴴ) 1 = fromBlocks (A - B * Bᴴ) 0 0 1 := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_add_neg]

theorem good_sum (hs : ∀ y : E, ‖star y‖ = ‖y‖) {m : Type} [Fintype m] [DecidableEq m] (H : Good m E)
    (G : Matrix (m ⊕ Unit) (m ⊕ Unit) E) (hG : G.IsHermitian) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (hGd : ‖G.det‖ = 1) (hk : G (Sum.inr ()) (Sum.inr ()) = 1) :
    ∃ h : Matrix (m ⊕ Unit) (m ⊕ Unit) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  have hD : G.toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩
    simp [toBlocks₂₂, hk]
  have hG' : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ 1 := by
    rw [← hD, fromBlocks_toBlocks]
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  have hh := hG
  rw [hG', isHermitian_fromBlocks_iff] at hh
  obtain ⟨hA, hBC, -, -⟩ := hh
  rw [← hBC] at hG'
  have hAi : Intg A := fun i j => hGi _ _
  have hBi : Intg B := fun i j => hGi _ _
  have hA'i : Intg (A - B * Bᴴ) := intg_sub hAi (intg_mul hBi (intg_conjT hs hBi))
  have hA'h : (A - B * Bᴴ).IsHermitian := hA.sub (isHermitian_mul_conjTranspose_self B)
  have hA'd : ‖(A - B * Bᴴ).det‖ = 1 := by
    rw [← det_fromBlocks_one₂₂, ← hG']
    exact hGd
  obtain ⟨h', hi', hd', hh'⟩ := H _ hA'h hA'i hA'd
  refine ⟨fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1, ?_, ?_, ?_⟩
  · exact intg_mul (intg_fromBlocks intg_one intg_zero (intg_neg (intg_conjT hs hBi)) intg_one)
      (intg_fromBlocks hi' intg_zero intg_zero intg_one)
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
    simp [hd']
  · rw [conjTranspose_mul, hG']
    calc (fromBlocks h' 0 0 1)ᴴ * (fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          (fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1)
        = (fromBlocks h' 0 0 1)ᴴ * ((fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          fromBlocks 1 0 (-Bᴴ) 1) * fromBlocks h' 0 0 1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [schur_conj]
        simp [fromBlocks_conjTranspose, fromBlocks_multiply, hh']

end Step

section Main

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem sol_transfer (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n n E) (h : Matrix n' n' E) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hd : ‖h.det‖ = 1) (hh : hᴴ * reindex e e G * h = 1) :
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  refine ⟨reindex e.symm e.symm h, fun i j => hi _ _, by rw [det_reindex_self]; exact hd, ?_⟩
  have : reindex e.symm e.symm (hᴴ * reindex e e G * h) = 1 := by rw [hh]; simp
  rw [← this]
  simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix]
  rw [← submatrix_mul_equiv (hᴴ * _) h e e e, ← submatrix_mul_equiv hᴴ _ e e e]
  simp

theorem good_all (hs : ∀ y : E, ‖star y‖ = ‖y‖)
    (piv : ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E), G.IsHermitian →
      Intg G → ‖G.det‖ = 1 → ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1) :
    ∀ (m : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = m → Good n E := by
  intro m
  induction m with
  | zero =>
    intro n _ _ hc G _ _ _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.1 hc
    refine ⟨1, fun i => isEmptyElim i, by simp, ?_⟩
    ext i
    exact isEmptyElim i
  | succ m ih =>
    intro n _ _ hc G hG hGi hGd
    haveI : Nonempty n := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨P, hPi, hPd, k, hk⟩ := piv n G hG hGi hGd
    have hM : (Pᴴ * G * P).IsHermitian := isHermitian_conjTranspose_mul_mul P hG
    have hMi : Intg (Pᴴ * G * P) := intg_mul (intg_mul (intg_conjT hs hPi) hGi) hPi
    have hMd : ‖(Pᴴ * G * P).det‖ = 1 := by
      rw [det_mul, det_mul, norm_mul, norm_mul, norm_det_conjT hs, hPd, hGd, one_mul, one_mul]
    let e : n ≃ {j // j ≠ k} ⊕ Unit :=
      (Equiv.optionSubtypeNe k).symm.trans (Equiv.optionEquivSumPUnit.{0, 0} _)
    have hc' : Fintype.card {j // j ≠ k} = m := by
      have := Fintype.card_congr (Equiv.optionSubtypeNe k)
      rw [Fintype.card_option] at this
      omega
    have hk' : reindex e e (Pᴴ * G * P) (Sum.inr ()) (Sum.inr ()) = 1 := by
      simpa [e, reindex_apply, Equiv.optionSubtypeNe] using hk
    obtain ⟨h, hi, hd, hh⟩ := good_sum hs (ih _ hc') (reindex e e (Pᴴ * G * P))
      (by simpa [reindex_apply] using hM.submatrix e.symm) (fun i j => hMi _ _)
      (by rw [det_reindex_self]; exact hMd) hk'
    obtain ⟨h₁, hi₁, hd₁, hh₁⟩ := sol_transfer hs e _ h hi hd hh
    refine ⟨P * h₁, intg_mul hPi hi₁, by rw [det_mul, norm_mul, hPd, hd₁, one_mul], ?_⟩
    rw [conjTranspose_mul, ← hh₁]
    simp only [Matrix.mul_assoc]

end Main

section Piv

theorem pivot_w {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hs : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he0 : ‖e0‖ ≤ 1) (he0' : e0 + star e0 = 1) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian) (hGi : Intg G)
    (hGd : ‖G.det‖ = 1) :
    ∃ i, ∃ w : n → E, (∀ a, ‖w a‖ ≤ 1) ∧ w i = 1 ∧ ‖star w ⬝ᵥ (G *ᵥ w)‖ = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitValueExistence.main
  | exact _root_.GlobalTheory.UnitValueExistence.main
  | (apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitValueExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitValueExistence.main ..)

end Piv

section Field

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem fixed_mem (a : E) (ha : star a = a) : ∃ u : F, algebraMap F E u = a := by
  let L : E →ₗ[F] E :=
    { toFun := fun y => star y - y
      map_add' := by
        intro x y
        simp only [star_add]
        abel
      map_smul' := by
        intro c y
        simp only [Algebra.smul_def, star_mul', Unram.star_fix, RingHom.id_apply, mul_sub] }
  have hfin : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hlt : LinearMap.ker L < ⊤ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    refine lt_top_iff_ne_top.2 fun h => hy ?_
    have : y ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simpa [L, sub_eq_zero] using this
  have h1 : Module.finrank F (LinearMap.ker L) < 2 := hfin ▸ Submodule.finrank_lt hlt.ne
  have hle : LinearMap.range (Algebra.linearMap F E) ≤ LinearMap.ker L := by
    rintro _ ⟨x, rfl⟩
    simp [L, Unram.star_fix]
  have hr : Module.finrank F (LinearMap.range (Algebra.linearMap F E)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (algebraMap F E).injective, Module.finrank_self]
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem : a ∈ LinearMap.ker L := by simp [L, ha]
  rw [← heq] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, hu⟩

theorem quad_col {n : Type} [Fintype n] (G P : Matrix n n E) (k : n) :
    (Pᴴ * G * P) k k = star (fun a => P a k) ⬝ᵥ (G *ᵥ fun a => P a k) := by
  simp only [mul_apply, dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

include F in
theorem pivot {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian)
    (hGi : Intg G) (hGd : ‖G.det‖ = 1) :
    ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1 := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hs : ∀ y : E, ‖star y‖ = ‖y‖ := Unram.norm_star (F := F)
  obtain ⟨-, ⟨e0, he0, he0'⟩, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  obtain ⟨i, w, hw, hwi, hq⟩ := pivot_w hs e0 he0 he0' G hG hGi hGd
  have ha : star (star w ⬝ᵥ (G *ᵥ w)) = star w ⬝ᵥ (G *ᵥ w) := by
    calc star (star w ⬝ᵥ (G *ᵥ w)) = (star w ᵥ* Gᴴ) ⬝ᵥ w := by rw [star_dotProduct, star_mulVec, star_star]
      _ = star w ⬝ᵥ (G *ᵥ w) := by rw [← dotProduct_mulVec, hG.eq]
  obtain ⟨u, hu⟩ := fixed_mem (F := F) _ ha
  have hu1 : ‖u‖ = 1 := by rw [← norm_algebraMap' E u, hu]; exact hq
  obtain ⟨v0, hv0⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E u hu1
  rw [hu] at hv0
  have hv0n : ‖v0‖ = 1 := by
    have h := congrArg norm hv0
    rw [norm_mul, hs, hq] at h
    nlinarith [norm_nonneg v0]
  have hv0ne : v0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv0n
    exact zero_ne_one hv0n
  have hc : ‖(star v0)⁻¹‖ = 1 := by rw [norm_inv, hs, hv0n, inv_one]
  refine ⟨(1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w), ?_, ?_, i, ?_⟩
  · intro p q
    rw [updateCol_apply]
    split_ifs
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
      exact hw p
    · exact intg_one p q
  · rw [← cramer_apply, cramer_one]
    simp [hc, hwi]
  · rw [quad_col]
    have hcol : (fun a => (1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w) a i) = (star v0)⁻¹ • w := by
      funext a
      simp
    have hst : star ((star v0)⁻¹ • w) = v0⁻¹ • star w := by
      funext p
      simp [star_mul', star_inv₀]
    rw [hcol, hst, smul_dotProduct, mulVec_smul, dotProduct_smul, ← hv0, smul_eq_mul, smul_eq_mul]
    have hsv : star v0 ≠ 0 := by rwa [star_ne_zero]
    field_simp

end Field

theorem unimodular_hermitian_eq_conj : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian →
    (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  intro F E _ _ _ _ _ s G hG hGi hGd
  haveI := Unram.ultraE (F := F) (E := E)
  exact good_all (Unram.norm_star (F := F)) (fun n _ _ _ G hG hGi hGd => pivot (F := F) (E := E) G hG hGi hGd) s (Fin s)
    (Fintype.card_fin s) G hG hGi hGd

end GlobalTheory.HermUnimod
