import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem hom_one {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G →* {r : ℝ // 0 < r}) (hc : Continuous φ) : ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [map_mul, mul_comm] at h
    exact (mul_le_iff_le_one_right' _).1 h
  intro u hu
  have h2 := hle _ (U.inv_mem hu)
  rw [map_inv, inv_le_one'] at h2
  exact le_antisymm (hle u hu) h2

private theorem ptF_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) := by
  have h : vFin (v ᵥ* γ.val) = vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul (algebraMap E (Af E)) γ.val v j
  change vFin v ᵥ* _ = vFin (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [IsTotallyComplex E]

private theorem pt_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val) := by
  have h : vInf (v ᵥ* γ.val) = vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul ((pInf E).comp (algebraMap E (Ad E))) γ.val v j
  change vInf v ᵥ* _ = vInf (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

private theorem rt_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem retract_rt (g : GA E a) : retractOne (rt g) = retractOne g := retractOne_coe _

private theorem ptF_rt (g : GA E a) : ptF (rt g) = ptF g := by
  have h : GeneralLinearGroup.map (pFin E) (rt g) = GeneralLinearGroup.map (pFin E) g := finPart_retract g
  refine AddMonoidHom.ext fun v => ?_
  change vFin v ᵥ* _ = vFin v ᵥ* _
  rw [h]

private theorem rt_fin (U : Subgroup (GL (Fin a) (Af E))) (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (g : GA E a) : rt (g * finGL E a u) = rt g * finGL E a u := by
  have h1 : Reduction.detModule E a (finGL E a u) = 1 := by
    rw [← Fb.finEmb_eq]
    exact hom_one U hU ((Reduction.detModule E a).comp (finEmb E a))
      (Reduction.continuous_detModule.comp continuous_finEmb) u hu
  unfold Lit.Geo.rt
  rw [coe_retractOne, coe_retractOne, map_mul, h1, mul_one, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

end

theorem UpperTheory.rationalPoint_retraction_exists_cmDatum :
    RtFacts := by
  intro E _ _ _ a _
  refine ⟨rt_left, fun g => ⟨congrArg Subtype.val (retract_rt g), ?_, ptF_rt g⟩,
    fun γ g v => ⟨ptF_rat γ g v, pt_rat γ g v⟩, rt_fin⟩
  unfold qht
  rw [retract_rt]
