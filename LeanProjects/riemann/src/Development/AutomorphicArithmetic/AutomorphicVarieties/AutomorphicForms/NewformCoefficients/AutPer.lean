import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem aff_comm {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 y * aff (1 : Rˣ) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem unip_eq {R : Type} [CommRing R] (x : BlockIx 2 1 → R) : unip x = aff 1 (x ⟨(0, 1), by decide⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 + nilM x : Matrix (Fin 2) (Fin 2) R) i j = _
  fin_cases i <;> fin_cases j <;> simp [aff, nilM]

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.autPer :
    UpperTheory.V.Af.Nf.AutPer := by
  intro φ hl ho g
  set t : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with ht
  have hc : Continuous fun x : Af ℚ => t⁻¹ * aff 1 x * t := (continuous_const.mul continuous_aff).mul continuous_const
  have h0 : t⁻¹ * aff 1 (0 : Af ℚ) * t ∈ {u | TR.finRep ℚ 2 u φ = φ} := by
    simp [aff_zero]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ)).eventually
    (ho.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun x => ?_⟩
  set N : ℕ := n.factorial with hN
  have hn' : ∀ g, φ.1 (g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e1 : g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * g :=
    TR.ga_ext (by simp) (by simp [← ht, mul_assoc])
  have e2 : unip x * finGL ℚ 2 (aff 1 (N : Af ℚ)) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * unip x :=
    TR.ga_ext (by simp) (by simp [unip_eq, map_aff, aff_comm])
  have e3 : ratGL ℚ 2 (aff 1 (N : ℚ)) = upR (aff 1 (N : ℝ)) * finGL ℚ 2 (aff 1 (N : Af ℚ)) := by
    rw [ratGL_eq, toR, toF, map_aff, map_aff, map_natCast, map_natCast]
  rw [← hn', ← hl (aff 1 (N : ℚ)) (unip x * g), e3, mul_assoc, mul_assoc, e1, mul_assoc, ← mul_assoc (unip x), e2, mul_assoc]
