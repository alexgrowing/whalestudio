import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

open scoped Pointwise

namespace GlobalTheory.SiegelBand

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

theorem le_pow_mul_of_adjacent {a : ℕ} (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {Q : ℝ} (hQ : 1 ≤ Q)
    (hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i) (i j : Fin a) :
    ρ i ≤ Q ^ a * ρ j := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have key : ∀ m : ℕ, ∀ i j : Fin a, (j : ℕ) = i + m → ρ i ≤ Q ^ m * ρ j ∧ ρ j ≤ Q ^ m * ρ i := by
    intro m
    induction m with
    | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      subst this
      simp
    | succ m ih =>
      intro i j h
      let j' : Fin a := ⟨i + m, by omega⟩
      obtain ⟨h1, h2⟩ := ih i j' rfl
      obtain ⟨h3, h4⟩ := hadj j' j (by simp [j']; omega)
      have hpm : 0 ≤ Q ^ m := pow_nonneg hQ0 m
      constructor
      · calc ρ i ≤ Q ^ m * ρ j' := h1
          _ ≤ Q ^ m * (Q * ρ j) := mul_le_mul_of_nonneg_left h3 hpm
          _ = Q ^ (m + 1) * ρ j := by ring
      · calc ρ j ≤ Q * ρ j' := h4
          _ ≤ Q * (Q ^ m * ρ i) := mul_le_mul_of_nonneg_left h2 hQ0
          _ = Q ^ (m + 1) * ρ i := by ring
  rcases le_total (i : ℕ) j with hij | hij
  · have h := (key ((j : ℕ) - i) i j (by omega)).1
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)
  · have h := (key ((i : ℕ) - j) j i (by omega)).2
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)

theorem absDetA_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    absDetA g = (ideleModule E (AdelicGLn.det E a g) : ℝ) := by
  unfold absDetA
  rw [Reduction.adeleAbs_units (K := E)]
  rfl

theorem posIdele_congr {E : Type} [Field E] [NumberField E] {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    Reduction.posIdele (K := E) x hx = Reduction.posIdele (K := E) y hy := by
  subst h; rfl

theorem exists_isCompact_band_siegel : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  intro E _ _ a ω hω t R ht
  classical
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hfc : Continuous fun b : GA E a => (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := Reduction.exists_pos_bounds hω hfc
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  set Q : ℝ := max 1 (max R t⁻¹) with hQdef
  have hQ : 1 ≤ Q := le_max_left _ _
  set Qa : ℝ := (Q ^ a) ^ a with hQadef
  have hQa : 0 < Qa := pow_pos (pow_pos (zero_lt_one.trans_le hQ) _) _
  set lo : ℝ := min 1 (X₁ / Qa) with hlodef
  set hi : ℝ := max 1 (Qa * X₂) with hhidef
  have hlo : 0 < lo := lt_min one_pos (div_pos hX₁ hQa)
  let g : {r : ℝ // 0 < r} → IdeleGroup E := fun r => Reduction.posIdele (K := E) r.1 r.2
  have hg : Continuous g := Reduction.continuous_posIdele_subtype
  let h : (Fin a → ℝ) → (Fin a → IdeleGroup E) := fun ρ i => g ⟨max (ρ i) lo, hlo.trans_le (le_max_right _ _)⟩
  have hh : Continuous h := continuous_pi fun i => hg.comp
      (((continuous_apply i).max continuous_const).subtype_mk fun ρ => hlo.trans_le (le_max_right _ _))
  let F : (Fin a → ℝ) → GA E a := fun ρ => Reduction.diagUnits a (h ρ)
  have hF : Continuous F := (Reduction.continuous_diagUnits (K := E) a).comp hh
  have hT : IsCompact (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) := (isCompact_univ_pi fun _ => isCompact_Icc).image hF
  have hband : band E a = {g | 1 ≤ (ideleModule E (AdelicGLn.det E a g) : ℝ)} ∩
      {g | (ideleModule E (AdelicGLn.det E a g) : ℝ) ≤ 2} := by
    ext g; simp [band, absDetA_eq]
  have hclosed : IsClosed (band E a) := by
    rw [hband]; exact (isClosed_le continuous_const hfc).inter (isClosed_le hfc continuous_const)
  refine ⟨ω * (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) * (Reduction.maxCompact (K := E) (n := a) : Set (GA E a)) ∩ band E a,
    ((hω.mul hT).mul Reduction.isCompact_maxCompact).inter_right hclosed, Set.inter_subset_right, ?_⟩
  intro b hb ρ hρ hlow hup k hk hmem
  refine ⟨?_, hmem⟩
  set P : ℝ := ∏ i, ρ i with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet := Reduction.det_mul_mul b (Reduction.diagUnits a fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) k
  rw [Reduction.ideleModule_det_diagUnits_posIdele ρ hρ,
    Reduction.mem_normOneGL.1 (Reduction.maxCompact_le_normOneGL hk), mul_one] at hdet
  have hm := hmem
  simp only [band, Set.mem_setOf_eq, absDetA_eq] at hm
  rw [hdet] at hm
  obtain ⟨h1, h2⟩ := hm
  have hbb := hB b hb
  have hPd1 : P ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc P ^ d * B₁ ≤ P ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hbb.1 (pow_nonneg hP.le _)
      _ = _ := mul_comm _ _
      _ ≤ 2 := h2
  have hPd2 : B₂⁻¹ ≤ P ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ B₂ * P ^ d := mul_le_mul_of_nonneg_right hbb.2 (pow_nonneg hP.le _)
  have hPlow : X₁ ≤ P := by
    rcases le_or_gt 1 P with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hPd2.trans (pow_le_of_le_one hP.le h.le hd0.ne'))
  have hPup : P ≤ X₂ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hPd1.trans (le_max_right _ _))
  have hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i := by
    intro i j hij
    constructor
    · exact (hup i j hij).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (hρ j).le)
    · calc ρ j = t⁻¹ * (t * ρ j) := by field_simp
        _ ≤ t⁻¹ * ρ i := mul_le_mul_of_nonneg_left (hlow i j hij) (inv_nonneg.2 ht.le)
        _ ≤ Q * ρ i := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (hρ i).le
  have hratio := le_pow_mul_of_adjacent ρ hρ hQ hadj
  have hbox : ∀ i, ρ i ∈ Set.Icc lo hi := by
    intro i
    have ha0 : a ≠ 0 := by have := i.2; omega
    have hup' : ρ i ^ a ≤ Qa * P := by
      calc ρ i ^ a = ∏ _j : Fin a, ρ i := by simp
        _ ≤ ∏ j : Fin a, (Q ^ a * ρ j) :=
          Finset.prod_le_prod (fun _ _ => (hρ i).le) fun j _ => hratio i j
        _ = Qa * P := by rw [Finset.prod_mul_distrib]; simp [hQadef, hPdef]
    have hlow' : P ≤ Qa * ρ i ^ a := by
      calc P = ∏ j : Fin a, ρ j := rfl
        _ ≤ ∏ _j : Fin a, (Q ^ a * ρ i) :=
          Finset.prod_le_prod (fun j _ => (hρ j).le) fun j _ => hratio j i
        _ = Qa * ρ i ^ a := by rw [Finset.prod_mul_distrib]; simp [hQadef]
    constructor
    · rcases le_or_gt 1 (ρ i) with h | h
      · exact (min_le_left _ _).trans h
      · refine (min_le_right _ _).trans ?_
        refine (pow_le_of_le_one (hρ i).le h.le ha0).trans' ?_
        rw [div_le_iff₀ hQa, mul_comm]
        exact hPlow.trans hlow'
    · rcases le_or_gt (ρ i) 1 with h | h
      · exact h.trans (le_max_left _ _)
      · exact (le_self_pow₀ h.le ha0).trans (hup'.trans
          ((mul_le_mul_of_nonneg_left hPup hQa.le).trans (le_max_right _ _)))
  have hFρ : F ρ = Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) := by
    show Reduction.diagUnits a (h ρ) = _
    congr 1
    funext i
    exact posIdele_congr _ _ (max_eq_left (hbox i).1)
  rw [← hFρ]
  exact Set.mul_mem_mul (Set.mul_mem_mul hb ⟨ρ, fun i _ => hbox i, rfl⟩) hk

end GlobalTheory.SiegelBand
