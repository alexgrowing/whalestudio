import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

noncomputable def upperConeRescale {E : Type} [Field E] (a : ℕ) (N : Matrix (Fin a) (Fin a) ℝ)
    (M : Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) :=
  Matrix.of fun p q => (fun _ => ((N p q : ℝ) : ℂ)) * M p q

lemma continuous_upperConeRescale {E : Type} [Field E] (a : ℕ) :
    Continuous (fun x : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin a) (Fin a) (Cinf E) => upperConeRescale a x.1 x.2) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [upperConeRescale, Matrix.of_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_pi fun _ => ?_
    exact Complex.continuous_ofReal.comp ((continuous_apply q).comp ((continuous_apply p).comp continuous_fst))
  · exact (continuous_apply q).comp ((continuous_apply p).comp continuous_snd)

lemma upperCone_conj_diag_eq {E : Type} [Field E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (d : GL (Fin a) (Cinf E)) (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M.BlockTriangular id) :
    (d⁻¹).val * M * d.val = upperConeRescale a (fun p q => if p ≤ q then r q / r p else 0) M := by
  have hD : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) := by
    have h1 : d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i x
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
      simp [this]
    calc (d⁻¹).val = (d⁻¹).val * (d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ))) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hD, hd]
  ext p q x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [upperConeRescale, Matrix.of_apply, Pi.mul_apply]
  by_cases hpq : p ≤ q
  · rw [if_pos hpq]
    have : (r p : ℂ) ≠ 0 := by exact_mod_cast (hr p).ne'
    push_cast
    field_simp
  · rw [if_neg hpq]
    have h0 : M p q = 0 := hM (lt_of_not_ge hpq)
    simp [h0]

end GlobalTheory

theorem GlobalTheory.upperCone_conj_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  intro E _ _ _ a ω hω htri t ht
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  set K : Set (Matrix (Fin a) (Fin a) ℝ) := Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (0:ℝ) C)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set A : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 x.2.val) '' (K ×ˢ ω)
  set B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 (x.2⁻¹).val) '' (K ×ˢ ω)
  have hAc : IsCompact A := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)))
  have hBc : IsCompact B := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_coe_inv.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (A ×ˢ (MulOpposite.op '' B)), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hAc.prod (hBc.image MulOpposite.continuous_op))
  intro r d hr hcone hd b hb
  have hN : (fun p q : Fin a => if p ≤ q then r q / r p else 0) ∈ K := by
    simp only [hK, Set.mem_pi]
    intro p _ q _
    rw [Set.mem_Icc]
    by_cases hpq : p ≤ q
    · simp only [if_pos hpq]
      exact ⟨div_nonneg (hr q).le (hr p).le, hC r hr hcone p q hpq⟩
    · simp only [if_neg hpq]
      exact ⟨le_rfl, hC0⟩
  have hbinv : (b⁻¹).val.BlockTriangular id := by
    have := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (htri b hb)
  refine ⟨?_, ?_⟩
  · refine ⟨(_, b), ⟨hN, hb⟩, ?_⟩
    simp only [Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd b.val (htri b hb)).symm
  · refine ⟨(d⁻¹ * b * d)⁻¹.val, ⟨(_, b), ⟨hN, hb⟩, ?_⟩, rfl⟩
    have : (d⁻¹ * b * d)⁻¹ = d⁻¹ * b⁻¹ * d := by group
    simp only [this, Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd (b⁻¹).val hbinv).symm
