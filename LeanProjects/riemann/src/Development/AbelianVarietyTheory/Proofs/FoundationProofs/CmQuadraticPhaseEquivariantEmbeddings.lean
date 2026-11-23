import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.QuadPhase

theorem exists_top_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let M₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : M₀ ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have hc : Countable M₀ := by
    have h1 := IntermediateField.cardinalMk_adjoin_le ℚ (S ∩ (M : Set ℂ))
    have h2 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0_iff.2 h2
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M₀)
    (algebraMap M₀ ℂ) ((ρ.comp (IntermediateField.inclusion hle)).toRingHom)
  refine ⟨((σ : ℂ →+* ℂ).toRatAlgHom).comp (IntermediateField.val ⊤), fun x hx hxM => ?_⟩
  have hx0 : x ∈ M₀ := IntermediateField.subset_adjoin ℚ _ ⟨hx, hxM⟩
  have h := hσ ⟨x, hx0⟩
  unfold cj TaylorLogMetric.liftM
  rw [dif_pos IntermediateField.mem_top, dif_pos hxM]
  exact h

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  unfold q1 gl3FieldFirst w0
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

theorem cmQuadraticForm_half_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x / 2 = gl3FieldFirst Λ (w0 D * x / 2) x := by
  rw [cmQuadraticForm_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [div_mul_eq_mul_div, Complex.div_ofNat_im]
  ring

theorem cmQuadraticForm_half_add_translation (D : D7) (Λ : AddSubgroup ℂ) (x l : ℂ) (m : ℕ) :
    q1 D Λ (x + 2 * (m : ℂ) * l) / 2 = q1 D Λ x / 2 + gl3FieldFirst Λ (w0 D * ((m : ℂ) * x)) l +
      gl3FieldFirst Λ (w0 D * l) ((m : ℂ) * x) + gl3FieldFirst Λ (w0 D * l) (((2 * m * m : ℕ) : ℂ) * l) := by
  rw [cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [← add_div, ← add_div, ← add_div, ← Complex.add_im, ← Complex.add_im, ← Complex.add_im]
  congr 2
  simp only [map_add, map_mul, map_natCast, map_ofNat]
  push_cast
  ring

theorem phase_top (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hc : Crv D cc δ) (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ)
    (x x' : ℂ) (m₀ : ℕ) (hm : 0 < m₀) (hx : (m₀ : ℂ) * x ∈ lamOf D cc δ)
    (hA : Adp1 ⊤ ρ (lamOf D cc δ) (2 * m₀) x x') :
    cj ⊤ ρ (ee (q1 D (lamOf D cc δ) x / 2)) = ee (q1 D (lamConj ⊤ ρ (lamOf D cc δ)) x' / 2) := by
  obtain ⟨hex, huniq, -, hadd, hmul, hord, -⟩ :=
    hS cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  have hWP := hW cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  set Λ := lamOf D cc δ with hΛ
  set Λ' := lamConj ⊤ ρ Λ with hΛ'
  have hm0 : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmulw : ∀ t t', StarPt ⊤ ρ Λ t t' → StarPt ⊤ ρ Λ (w0 D * t) (w0 D * t') := fun t t' h => by
    have := hmul a t t' h
    rwa [ha] at this
  have hw : ∀ l ∈ Λ, w0 D * l ∈ Λ := fun l hl => by
    have h := hmulw l 0 (Or.inl ⟨hl, zero_mem _⟩)
    rcases h with h | h
    · exact h.1
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.2.1
  have hw' : ∀ l ∈ Λ', w0 D * l ∈ Λ' := fun l hl => by
    have h := hmulw 0 l (Or.inl ⟨zero_mem _, hl⟩)
    rcases h with h | h
    · exact h.2
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.1
  have hint : ∀ l ∈ Λ', ∀ l' ∈ Λ', ee (gl3FieldFirst Λ' l l') = 1 := fun l hl l' hl' => by
    have h := hWP 0 0 l l' 1 one_pos (by simp) (by simp)
      (Or.inl ⟨by simp, by simpa using hl⟩) (Or.inl ⟨by simp, by simpa using hl'⟩) IntermediateField.mem_top
    rw [← h]
    have h0 : gl3FieldFirst Λ 0 0 = 0 := by simp [gl3FieldFirst]
    rw [h0, ee_zero]
    unfold cj TaylorLogMetric.liftM
    rw [dif_pos IntermediateField.mem_top]
    exact map_one ρ
  have hnat : ∀ (A : AddSubgroup ℂ) (n : ℕ), ∀ l ∈ A, (n : ℂ) * l ∈ A := fun A n l hl => by
    rw [← nsmul_eq_mul]
    exact nsmul_mem hl n
  have htn : ((4 * m₀ * m₀ : ℕ) : ℂ) * (x / (4 * (m₀ : ℂ))) = (m₀ : ℂ) * x := by
    push_cast
    field_simp
  obtain ⟨t', ht'⟩ := hex (x / (4 * (m₀ : ℂ))) ⟨4 * m₀ * m₀, by positivity, htn ▸ hx⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  set y : ℂ := 4 * (m₀ : ℂ) * t' with hy
  have hA2 : Adp1 ⊤ ρ Λ (2 * m₀) x y := by
    have h := hadd _ _ _ _ ht' ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hA3 : Adp1 ⊤ ρ Λ (2 * m₀) (w0 D * x / 2) (w0 D * y / 2) := by
    have h := hmulw _ _ ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hl := (huniq _ _ _ hA).1 hA2
  have hμ : (m₀ : ℂ) * y ∈ Λ' := by
    have h := (hord (4 * m₀ * m₀) _ _ ht').1 (htn ▸ hx)
    convert h using 1
    rw [hy]
    push_cast
    ring
  set l : ℂ := x' / ((2 * m₀ : ℕ) : ℂ) - y / ((2 * m₀ : ℕ) : ℂ) with hldef
  have hx' : x' = y + 2 * (m₀ : ℂ) * l := by
    rw [hldef]
    push_cast
    field_simp
    ring
  have hmain := hWP (w0 D * x / 2) x (w0 D * y / 2) y (2 * m₀) (by positivity)
    (by
      convert hw _ hx using 1
      push_cast
      ring)
    (by
      convert hnat Λ 2 _ hx using 1
      push_cast
      ring)
    hA3 hA2 IntermediateField.mem_top
  rw [hx', cmQuadraticForm_half_add_translation, ee_add, ee_add, ee_add, hint _ (hw' _ hμ) _ hl, hint _ (hw' _ hl) _ hμ,
    hint _ (hw' _ hl) _ (hnat Λ' _ _ hl), cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm, hmain]
  simp

theorem galPh1_of (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) : galPh1 D := by
  intro cc δ hc
  refine ⟨fun x => cmQuadraticForm_eq_alternatingForm D _ x, fun M ρ hK h2 h3 x x' m₀ hm hx hA he => ?_⟩
  set Λ := lamOf D cc δ with hΛ
  have hKc : Countable D.host.K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let S : Set ℂ := Set.range (fun a : D.host.K => D.host.φ₀ (a : D.host.E)) ∪
    {g2 Λ, g3 Λ, wpF Λ (x / ((2 * m₀ : ℕ) : ℂ)), wpD Λ (x / ((2 * m₀ : ℕ) : ℂ)), ee (q1 D Λ x / 2)}
  have hSc : S.Countable := (Set.countable_range _).union (Set.toFinite _).countable
  obtain ⟨σ, hσ⟩ := exists_top_extension M ρ S hSc
  have hK' : FixK D ⊤ σ := fun a =>
    ⟨IntermediateField.mem_top, by rw [hσ _ (Or.inl ⟨a, rfl⟩) (hK a).1, (hK a).2]⟩
  have hl : lamConj ⊤ σ Λ = lamConj M ρ Λ := by
    have e2 := hσ (g2 Λ) (Or.inr (by simp)) h2
    have e3 := hσ (g3 Λ) (Or.inr (by simp)) h3
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hA' : Adp1 ⊤ σ Λ (2 * m₀) x x' := by
    unfold Adp1 StarPt at hA ⊢
    rw [hl]
    rcases hA with h | ⟨h1, h2', h3', h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2', IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hσ _ (Or.inr (by simp)) h3']
      · rw [h6, hσ _ (Or.inr (by simp)) h4]
  have h := phase_top D hS hW cc δ hc σ hK' x x' m₀ hm hx hA'
  rw [← hΛ, hl, hσ _ (Or.inr (by simp)) he] at h
  exact h

theorem galPh1_all : ∀ D : D7, galPh1 D := fun D =>
  galPh1_of D (GlobalTheory.T.galStar_complexMultiplication_points D) (GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion D)

end GlobalTheory.QuadPhase
