import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsApprox
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.StabFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.PvFinHolds

open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.kFinMem_holds :
    UpperTheory.V.KernelIndexFullLattice.KFinMem := by
  intro K _ _ n μ₁ _ π v hv hop hfin
  have h1 : retractOne (1 : AdelicGLn.AdelicGL K n) = 1 := retractOne_coe (1 : Reduction.normOneGL K n)
  let r : AdelicGLn.FiniteAdelicGL K n →* Reduction.normOneGL K n :=
    { toFun := fun h => retractOne (finEmb K n h)
      map_one' := by rw [map_one, h1]
      map_mul' := fun a b => by rw [map_mul, retractOne_mul] }
  let S : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | cuspRepT μ₁ (r h) v = v}
      one_mem' := by
        show cuspRepT μ₁ (r 1) v = v
        rw [map_one r]
        simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        have hb' : cuspRepT μ₁ (r b) v = v := hb
        show cuspRepT μ₁ (r (a * b)) v = v
        rw [map_mul r, UnitaryRep.map_mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        show cuspRepT μ₁ (r a⁻¹) v = v
        have h := (cuspRepT μ₁).map_mul_apply (r a⁻¹) (r a) v
        rw [ha', ← map_mul r, inv_mul_cancel, map_one r] at h
        rw [← h]
        simp }
  have hSo : IsOpen (S : Set (AdelicGLn.FiniteAdelicGL K n)) := hop
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) := S ⊓ AdelicGLn.integralFiniteGL K n
  have hUo : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := hSo.inter (AdelicGLn.isOpen_integralFiniteGL K n)
  have hUc : IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_holds K n μ₁ π U hUc hUo v (fun u hu => hu.1) hfin
  let A : archCompact K n ⊕ U → CuspL2 μ₁ →L[ℂ] CuspL2 μ₁ :=
    Sum.elim (fun k => cuspRepT μ₁ (archP K n k)) fun u => cuspRepT μ₁ (r u)
  refine UpperTheory.V.KernelIndexFullLattice.absApprox_holds (archCompact K n ⊕ U) (CuspL2 μ₁) A ?_ _ N hN ?_ v hv
    fun P hP hPW => hN' P (fun k x => hP (.inl k) x) (fun u hu x => hP (.inr ⟨u, hu⟩) x) hPW
  · rintro (k | u)
    · refine ⟨.inl k⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (archP K n k)) = cuspRepT μ₁ (archP K n (k : archGroup K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv (archP K n)]
    · refine ⟨.inr u⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (r u)) =
        cuspRepT μ₁ (r (u : AdelicGLn.FiniteAdelicGL K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv r]
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨Y, hY, hφY, hk, hu⟩ :=
      UpperTheory.V.KernelIndexFullLattice.stabFin_holds K n π.carrier π.toModule π.isAdmissible.1 U hUc ⟨φ, hφ⟩
    let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
    refine ⟨Y.map j, ?_, inferInstance, ⟨_, hφY, rfl⟩, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro (k | u) _ ⟨y, hy, rfl⟩
      · exact ⟨_, hk k y hy, cuspToL2_sigma μ₁ k (π.le_central y.2)⟩
      · exact ⟨_, hu u u.2 y hy, cuspToL2_finRepCusp μ₁ u (π.le_central y.2)⟩
