import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix Topology

namespace UpperTheory.V.Sd

private theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

private theorem exists_sign (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (d : (TR.Rinf F)ˣ) :
    ∃ a : Fˣ, ∀ v, 0 < ((TR.pInf F).comp (algebraMap F (Ad F)) (a : F)) v * (d : TR.Rinf F) v := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have hd : DenseRange ((TR.pInf F).comp (algebraMap F (Ad F))) :=
    (TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc
  have ho : IsOpen {x : TR.Rinf F | ∀ v, 0 < x v * (d : TR.Rinf F) v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  have hne : ∀ v, (d : TR.Rinf F) v ≠ 0 := fun v h => by
    have := congrFun d.mul_inv v
    simp [h] at this
  obtain ⟨a, ha⟩ := hd.exists_mem_open ho ⟨d, fun v => mul_self_pos.2 (hne v)⟩
  refine ⟨Units.mk0 a ?_, ha⟩
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using ha v

private theorem exists_sl (F : Type) [Field F] [NumberField F] (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ GeneralLinearGroup.det σ = 1 ∧
      g = GeneralLinearGroup.map (algebraMap F (Af F)) σ * (aff y 0 * u) := by
  set y := GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff, hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.strongApp :
    UpperTheory.V.Sd.StrongApp := by
  intro F _ _ _ K hK g
  set j := (TR.pInf F).comp (algebraMap F (Ad F)) with hj
  set gi := GeneralLinearGroup.map (TR.pInf F) g with hgi
  obtain ⟨a, ha⟩ := exists_sign F (GeneralLinearGroup.det gi)
  obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl F K hK
    ((GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0))⁻¹ * GeneralLinearGroup.map (pFin F) g)
  have hγ : GeneralLinearGroup.det (aff a 0 * σ) = a := by rw [map_mul, det_aff, hσ, mul_one]
  set h := (GeneralLinearGroup.map j (aff a 0 * σ))⁻¹ * gi with hh
  have hh' : GeneralLinearGroup.map j (aff a 0 * σ) * h = gi := by rw [hh, mul_inv_cancel_left]
  have e' : GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0 * σ) * (aff y 0 * u) =
      GeneralLinearGroup.map (pFin F) g := by
    rw [inv_mul_eq_iff_eq_mul.1 e, map_mul, mul_assoc]
  generalize aff a 0 * σ = γ at *
  refine ⟨γ, h, y, u, hu, fun v => ?_, TR.ga_ext ?_ ?_⟩
  · have h1 := ha v
    rw [← hh', map_mul, Units.val_mul, GlobalTheory.CuspRep.det_map, hγ, Pi.mul_apply, ← hj, ← mul_assoc] at h1
    exact (pos_iff_pos_of_mul_pos h1).1 (lt_of_le_of_ne (mul_self_nonneg _) fun h0 => by simp [← h0] at h1)
  · rw [map_mul, map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, ← hgi, ← hh']
    rfl
  · rw [map_mul, map_mul, TR.pFin_infGL, one_mul, ← e']
    congr 1
    simp
