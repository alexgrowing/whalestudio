import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem ev_int_exsplit {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).eventually

theorem coeff_zero_ne_zero_of_mem_ell {E : Type} [Field E] [NumberField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨hmon, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hne : P.map τ ≠ 0 := (hmon.map τ).ne_zero
  have hr : (0 : ℂ) ∈ (P.map τ).roots := by
    rw [mem_roots hne, IsRoot.def, eval_map, eval₂_at_zero, h0, map_zero]
  have := hroots τ 0 hr
  simp at this

theorem exists_mat_charpoly {E : Type} [Field E] {n : ℕ} {P : E[X]} (hmon : P.Monic) (hdeg : P.natDegree = n) :
    ∃ M : Matrix (Fin n) (Fin n) E, M.charpoly = P := by
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have hdim : pb.dim = n := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix pb.basis pb.gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon]

theorem exists_int_charpoly_atPl_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ _ n _ P hP
  obtain ⟨M, hM⟩ := exists_mat_charpoly hP.1 hP.2.1
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (coeff_zero_ne_zero_of_mem_ell hP)
  have hev1 : ∀ᶠ w : Pl E in cofinite, ∀ ij : Fin n × Fin n,
      algebraMap E (w.adicCompletion E) (M ij.1 ij.2) ∈ w.adicCompletionIntegers E :=
    Filter.eventually_all.2 fun ij => ev_int_exsplit (M ij.1 ij.2)
  have hev2 := ev_int_exsplit (E := E) M.det⁻¹
  filter_upwards [hev1, hev2] with w hent hinv hs
  let N : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨_, hent (i, j)⟩
  have hN : (Ov E w).subtype.mapMatrix N = M.map (algebraMap E (w.adicCompletion E)) := by
    ext i j; rfl
  have hdetN : ((N.det : Ov E w) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) M.det := by
    have := RingHom.map_det (Ov E w).subtype N
    rw [hN] at this
    exact this.trans (RingHom.map_det _ M).symm
  have hu : IsUnit N.det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    change ((N.det : Ov E w) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) M.det⁻¹ = 1
    rw [hdetN, ← map_mul, mul_inv_cancel₀ hdet, map_one]
  let g : GL (Fin n) (Ov E w) := ((Matrix.isUnit_iff_isUnit_det N).2 hu).unit
  have hmemU : bc (Ov E w).subtype g ∈ UL n w := by
    simp only [UL, if_pos hs]; exact Subgroup.mem_top _
  refine ⟨⟨_, hmemU⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    exact ⟨g, rfl⟩
  · change ((Ov E w).subtype.mapMatrix (g : Matrix (Fin n) (Fin n) (Ov E w))).charpoly = atPl w P
    rw [IsUnit.unit_spec, hN, Matrix.charpoly_map, hM]

end GlobalTheory.BCT
