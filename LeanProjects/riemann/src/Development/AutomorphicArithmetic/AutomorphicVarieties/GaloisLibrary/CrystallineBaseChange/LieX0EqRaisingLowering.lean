import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RotEig

open NumberField GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.WeightVectorLie

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (t : ℝ) : TR.Kinf F 2 :=
  ⟨!![fun _ => Real.cos t, fun _ => Real.sin t; fun _ => -Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]⟩

omit [NumberField F] in
private theorem rot_zero : rot 0 = (1 : TR.Kinf F 2) := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

private noncomputable def X0 : TR.Lie F 2 := TR.toL !![0, 1; -1, 0]

private theorem lie_X0_eq_raising_lowering [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (v : InfinitePlace F) (φ : TR.Sm F 2) :
    TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = TR.lie F 2 X0 φ := by
  unfold TR.Eop
  rw [← LinearMap.sub_apply, ← map_sub]
  congr 2
  ext i j u
  obtain rfl : u = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp [X0]

private theorem rot_deriv : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (F := F) t)).val) X0 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  fin_cases i <;> fin_cases j
  · simpa [X0, rot] using Real.hasDerivAt_cos 0
  · simpa [X0, rot] using Real.hasDerivAt_sin 0
  · simpa [X0, rot] using (Real.hasDerivAt_sin 0).fun_neg
  · simpa [X0, rot] using Real.hasDerivAt_cos 0

private theorem lie_mem [IsTotallyReal F] (U : Submodule ℂ (TR.Sm F 2)) [FiniteDimensional ℂ U]
    (hU : ∀ k, ∀ ψ ∈ U, TR.cptRep F 2 k ψ ∈ U) (ψ : TR.Sm F 2) (hψ : ψ ∈ U) : TR.lie F 2 X0 ψ ∈ U := by
  let U' : Submodule ℂ (GA F 2 → ℂ) := U.map (TR.Sm F 2).subtype
  have hcl : IsClosed (U' : Set (GA F 2 → ℂ)) := U'.closed_of_finiteDimensional
  have key : ∀ g, HasDerivAt (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) ((TR.lie F 2 X0 ψ).1 g) 0 := fun g =>
    TR.hasDerivAt_curve ψ g (fun t => Unitary.toUnits (rot t)) X0 (by rw [rot_zero, map_one]) rot_deriv
  have hm : (TR.lie F 2 X0 ψ).1 ∈ U' := by
    refine hcl.mem_of_tendsto (b := nhdsWithin (0 : ℝ) {0}ᶜ)
      (f := fun t g => slope (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) 0 t)
      (tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (key g)) (Filter.Eventually.of_forall fun t => ?_)
    exact U'.smul_of_tower_mem ((t - 0)⁻¹ : ℝ)
      (U'.sub_mem (Submodule.mem_map_of_mem (hU (rot t) ψ hψ)) (Submodule.mem_map_of_mem (hU (rot 0) ψ hψ)))
  obtain ⟨χ, hχ, e⟩ := hm
  rwa [← Subtype.ext e]

private theorem eig_abs {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (D : Module.End ℂ M)
    (hD : ∀ U : Submodule ℂ M, FiniteDimensional ℂ U → (∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U) → ∀ ψ ∈ U, D ψ ∈ U)
    (V : Submodule ℂ M) (φ : M) (hφ0 : φ ≠ 0) (hV : ∀ k, ρ k φ ∈ V)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k φ))) :
    ∃ ψ ∈ V, ψ ≠ 0 ∧ ∃ z : ℂ, D ψ = z • ψ := by
  let U : Submodule ℂ M := Submodule.span ℂ (Set.range fun k => ρ k φ)
  have hUV : U ≤ V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hV k)
  have hU : ∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U := fun k ψ hψ => by
    have h : U ≤ U.comap (ρ k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      exact Submodule.subset_span ⟨k * k', by simp⟩)
    exact h hψ
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial U := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (D.restrict (hD U hf hU))
  obtain ⟨ψ, hψ⟩ := hz.exists_hasEigenvector
  exact ⟨ψ.1, hUV ψ.2, fun h => hψ.2 (Subtype.ext h), z, congrArg Subtype.val hψ.apply_eq_smul⟩

private theorem act_cpt [IsTotallyReal F] (k : TR.Kinf F 2) : TR.act (.cpt k) = TR.cptRep F 2 k := by
  rw [TR.act]

private theorem eig [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (π : TR.CuspSub F 2) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ z : ℂ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨ψ, h1, h2, z, h3⟩ := eig_abs (TR.cptRep F 2) (TR.lie F 2 X0) (fun U _ hU => lie_mem U hU) π.V φ hφ0
    (fun k => by rw [← act_cpt]; exact π.stable _ φ hφ) (π.cusp φ hφ).1.kfin
  exact ⟨ψ, h1, h2, z, fun v => (lie_X0_eq_raising_lowering v ψ).trans h3⟩

private theorem int_of [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (ψ : TR.Sm F 2) (h0 : ψ ≠ 0) (z : ℂ)
    (he : ∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = z • ψ) : ∃ n : ℤ, z = Complex.I * n := by
  have hr : IsRot (F := F) (fun _ => 2 * Real.pi) 1 := by
    ext i j v
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨g, hg⟩ : ∃ g, ψ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  have h1 := rotEig F ψ z he _ _ hr g
  rw [map_one, mul_one] at h1
  have h2 : Complex.exp (z * (2 * Real.pi)) = 1 := by
    have h3 := mul_right_cancel₀ hg (h1.symm.trans (one_mul _).symm)
    have : Unique (InfinitePlace F) := uniqueOfSubsingleton (Classical.arbitrary _)
    simpa using h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply mul_right_cancel₀ hpi
  rw [hn]; ring

end UpperTheory.V.Br.WeightVectorLie

open UpperTheory.V.Br.WeightVectorLie in
theorem UpperTheory.V.Br.wtVec :
    UpperTheory.V.Br.WtVec := by
  intro π
  obtain ⟨φ, hφ, h0, z, he⟩ := eig π
  obtain ⟨n, rfl⟩ := int_of φ h0 z he
  exact ⟨φ, hφ, h0, n, he⟩
