import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lrep_repU_of_dvd (M l : ℕ) (hl : l.Prime) (hlM : l ∣ M) :
    LRep M {δ : M2 | δ.det = l ∧ (M : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} (repU l) := by
  have hlM' : (l : ℤ) ∣ (M : ℤ) := by exact_mod_cast hlM
  have hpZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have key : ∀ γ : SL(2, ℤ), (M : ℤ) ∣ (γ : M2) 1 0 → ¬ (l : ℤ) ∣ (γ : M2) 0 0 := by
    intro γ hc ha
    have hdet : (γ : M2).det = 1 := γ.2
    rw [Matrix.det_fin_two] at hdet
    have : (l : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right (hlM'.trans hc) _)
    exact hpZ.not_dvd_one this
  have ent : ∀ (A : M2) (j : Fin l), (A * repU l j) 0 0 = A 0 0 ∧ (A * repU l j) 1 0 = A 1 0 ∧
      (A * repU l j) 0 1 = A 0 0 * (j : ℕ) + A 0 1 * l ∧
      (A * repU l j) 1 1 = A 1 0 * (j : ℕ) + A 1 1 * l := by
    intro A j
    simp [repU, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨γ, hγ⟩, j⟩ -
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, -, -⟩ := ent (γ : M2) j
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul, repU, Matrix.det_fin_two_of]
      rw [show (γ : M2).det = 1 from γ.2]
      simp
    · simpa [e2] using hc
    · simpa [e1] using key γ hc
  · rintro ⟨⟨γ, hγ⟩, j⟩ - ⟨⟨γ', hγ'⟩, j'⟩ - h
    simp only at h
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    obtain ⟨f1, f2, f3, f4⟩ := ent (γ' : M2) j'
    have h00 : (γ : M2) 0 0 = (γ' : M2) 0 0 := by rw [← e1, ← f1, h]
    have h10 : (γ : M2) 1 0 = (γ' : M2) 1 0 := by rw [← e2, ← f2, h]
    have h01 : (γ : M2) 0 0 * (j : ℕ) + (γ : M2) 0 1 * l = (γ' : M2) 0 0 * (j' : ℕ) + (γ' : M2) 0 1 * l := by
      rw [← e3, ← f3, h]
    have h11 : (γ : M2) 1 0 * (j : ℕ) + (γ : M2) 1 1 * l = (γ' : M2) 1 0 * (j' : ℕ) + (γ' : M2) 1 1 * l := by
      rw [← e4, ← f4, h]
    have hdiv : (l : ℤ) ∣ (γ : M2) 0 0 * (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) :=
      ⟨(γ' : M2) 0 1 - (γ : M2) 0 1, by rw [h00] at h01 ⊢; linear_combination h01⟩
    have hd2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) :=
      (hpZ.dvd_or_dvd hdiv).resolve_left (key γ hc)
    have hjj : j = j' := by
      have hj := j.2
      have hj' := j'.2
      obtain ⟨k, hk⟩ := hd2
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      subst hk0
      ext
      omega
    subst hjj
    have g01 : (γ : M2) 0 1 = (γ' : M2) 0 1 := by
      apply mul_right_cancel₀ hl0; rw [h00] at h01; linarith
    have g11 : (γ : M2) 1 1 = (γ' : M2) 1 1 := by
      apply mul_right_cancel₀ hl0; rw [h10] at h11; linarith
    have : γ = γ' := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [h00, h10, g01, g11]
    subst this
    rfl
  · rintro δ ⟨hdet, hc, ha⟩
    haveI : Fact l.Prime := ⟨hl⟩
    have hlc : (l : ℤ) ∣ δ 1 0 := hlM'.trans hc
    rw [Matrix.det_fin_two] at hdet
    have hld : (l : ℤ) ∣ δ 1 1 := by
      have : (l : ℤ) ∣ δ 0 0 * δ 1 1 := ⟨1 + (δ 0 1) * ((δ 1 0) / l), by
        obtain ⟨t, ht⟩ := hlc
        rw [ht, Int.mul_ediv_cancel_left _ hl0]
        linear_combination hdet + (δ 0 1) * ht⟩
      exact (hpZ.dvd_or_dvd this).resolve_left ha
    have haZ : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha
    let j : Fin l := ⟨(((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩
    have hjZ : ((j : ℕ) : ZMod l) = ((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ :=
      ZMod.natCast_zmod_val _
    have hb : (l : ℤ) ∣ δ 0 1 - δ 0 0 * (j : ℕ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjZ]
      field_simp
      ring
    have hdd : (l : ℤ) ∣ δ 1 1 - δ 1 0 * (j : ℕ) := dvd_sub hld (dvd_mul_of_dvd_left hlc _)
    obtain ⟨e, he⟩ := hb
    obtain ⟨f, hf⟩ := hdd
    have hγdet : (!![δ 0 0, e; δ 1 0, f] : M2).det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hl0
      linear_combination -(δ 0 0) * hf + (δ 1 0) * he + hdet
    let γ : SL(2, ℤ) := ⟨!![δ 0 0, e; δ 1 0, f], hγdet⟩
    have hγ : γ ∈ Gamma0 M := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [γ] using hc)
    refine ⟨(⟨γ, hγ⟩, j), Set.mem_univ _, ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    ext i k; fin_cases i <;> fin_cases k
    · simpa [γ] using e1
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e3 ⊢
      rw [e3]; simp [γ]; linarith
    · simpa [γ] using e2
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e4 ⊢
      rw [e4]; simp [γ]; linarith

theorem lrep_repU (L l : ℕ) (hl : l.Prime) :
    (l ∣ L → LRep L (DU L l) (repU l)) ∧
      (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  refine ⟨fun h => lrep_repU_of_dvd L l hl h, fun _ => ?_⟩
  have hs : {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} =
      {δ : M2 | δ.det = l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} := by
    ext δ
    simp only [DU, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, (Int.natCast_dvd_natCast.mpr (dvd_mul_right L l)).trans h4, h3⟩, h4⟩
  rw [hs]
  exact lrep_repU_of_dvd (L * l) l hl (dvd_mul_left l L)

theorem zrepU : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧
    (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) :=
  fun L l hl => lrep_repU L l hl

end GlobalTheory.EisM
