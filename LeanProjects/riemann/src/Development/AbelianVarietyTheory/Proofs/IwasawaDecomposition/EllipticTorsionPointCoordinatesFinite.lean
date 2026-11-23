import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory

theorem finite_latticeCurve_torsion (L : PeriodPair) {n : ℕ} (hn : n ≠ 0) :
    {P : (latticeCurve L).toAffine.Point | n • P = 0}.Finite := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hz : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine (((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image
    (fun p : ℤ × ℤ => latticePoint L ((p.1 * L.ω₁ + p.2 * L.ω₂) / n))).subset ?_
  intro P hP
  obtain ⟨z, rfl⟩ := latticePoint_surjective L P
  have h1 : latticePoint L (n • z) = 0 := by
    rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
  rw [latticePoint_eq_zero_iff] at h1
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩,
    ⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩⟩, ?_⟩
  dsimp only
  rw [latticePoint_eq_iff, PeriodPair.mem_lattice]
  refine ⟨-(a / n), -(b / n), ?_⟩
  have ea : (a : ℂ) = ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a n).symm
  have eb : (b : ℂ) = ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b n).symm
  rw [nsmul_eq_mul] at hab
  rw [Int.cast_neg, Int.cast_neg]
  generalize ((a % n : ℤ) : ℂ) = a₁, ((a / n : ℤ) : ℂ) = a₂, ((b % n : ℤ) : ℂ) = b₁,
    ((b / n : ℤ) : ℂ) = b₂ at ea eb ⊢
  rw [ea, eb] at hab
  field_simp
  linear_combination -hab

theorem finite_complex_torsion_points (W : WeierstrassCurve ℂ) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.toAffine.Point | n • P = 0}.Finite := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  refine ((finite_latticeCurve_torsion L hn).image e).subset ?_
  intro P hP
  refine ⟨e.symm P, ?_, e.apply_symm_apply P⟩
  have hP' : n • P = 0 := hP
  show n • e.symm P = 0
  rw [← map_nsmul, hP', map_zero]

theorem finite_torsionCoords :
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  intro W _ n hn
  have h := finite_complex_torsion_points W hn
  let fx : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some x _ _ => x
  let fy : W.toAffine.Point → ℂ := fun P => match P with
    | .zero => 0
    | .some _ y _ => y
  refine ((h.image fx).union (h.image fy)).subset ?_
  rintro z ⟨x, y, hxy, h0, rfl | rfl⟩
  · exact Or.inl ⟨_, h0, rfl⟩
  · exact Or.inr ⟨_, h0, rfl⟩

end GlobalTheory
