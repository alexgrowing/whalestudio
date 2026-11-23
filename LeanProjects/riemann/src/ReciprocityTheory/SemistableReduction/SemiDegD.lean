import ReciprocityTheory.SemistableReduction.SemiDegDA
import ReciprocityTheory.SemistableReduction.SemiDegDB

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l

theorem sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle

theorem gradedExt_holds (hB : LatDegBasisStatement) (hD : DegAddStatement) :
    GradedExtStatement := by
  unfold GradedExtStatement
  unfold LatDegBasisStatement at hB
  unfold DegAddStatement at hD
  intro K _ _ r e k k₀ k₁ δ B b b₀ b₁ hδ hFG hb hb₀ hb₁

  have hlift : ∀ j, ∃ y ∈ B, projGe K r e y = b₁ j := fun j => Submodule.mem_map.mp (hb₁.1 j)
  choose c hcB hcb using hlift
  have hb₀B : ∀ i, b₀ i ∈ B := fun i => (hb₀.1 i).1
  have hb₀cut : ∀ i, b₀ i ∈ cutSub K r e := fun i => (hb₀.1 i).2
  have hli : LinearIndependent K (Fin.append b₀ c) :=
    sdd_append_li b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
  have hsp : ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) :=
    sdd_append_span B b₀ c b₁ hb₀ hcB hcb hb₁
  have hmem : ∀ i, Fin.append b₀ c i ∈ B := by
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hb₀B, hcB]
  have hk : k = k₀ + k₁ := sdd_card_eq B b (Fin.append b₀ c) hb hmem hli hsp
  subst hk
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ => by
    simp only [diagMet]
    exact posDef_diagonal_ofReal_of_pos (δ σ) (hδ σ)
  have h1 : latDeg (diagMet δ) B b = latDeg (diagMet δ) B (Fin.append b₀ c) :=
    hB K r (k₀ + k₁) (diagMet δ) B b (Fin.append b₀ c) hpd hFG hb ⟨hmem, hli, hsp⟩
  have h2 := hD K r k₀ k₁ (diagMet δ) B b₀ c hpd hFG hb₀B hcB hli hsp
  have hsat : satSub B b₀ = B ⊓ cutSub K r e := sdd_satSub_eq B b₀ hb₀
  rw [hsat] at h2
  have h3 : quotDeg (diagMet δ) B b₀ c ≤ latDeg (diagMet δ) (B.map (projGe K r e)) b₁ := by
    unfold quotDeg latDeg
    rw [sdd_index B b₀ c b₁ hsat hcB hcb]
    have hs : ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ b₁).det.re ≤
        ∑ σ : K →+* ℂ, Real.log (quotGramC (diagMet δ σ) σ b₀ c).det.re :=
      Finset.sum_le_sum fun σ _ =>
        sdd_gram_step σ (δ σ) (hδ σ) b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
    linarith
  linarith [h1, h2, h3]

theorem absDet_holds : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h

end ReciprocityTheory.MultiplicativeHeights
