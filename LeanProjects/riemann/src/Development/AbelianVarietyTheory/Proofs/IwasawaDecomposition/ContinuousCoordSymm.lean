import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedCoord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def coord (S T : HSp D) : WO S T ≃+ WA S T where
  toFun := toTWsmall S T
  invFun y := HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D))
  left_inv x := by
    simp only [toTWsmall, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv y := by
    simp only [toTWsmall]
    rw [Matrix.mul_assoc, mul_gramInv, Matrix.mul_one, Matrix.transpose_transpose]
  map_add' x y := by
    simp only [toTWsmall]
    rw [Matrix.add_mul, Matrix.transpose_add]

theorem coord_apply (S T : HSp D) (x : WO S T) :
    coord S T x = (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D)))ᵀ := rfl

theorem coord_symm_apply (S T : HSp D) (y : WA S T) :
    (coord S T).symm y = HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D)) := rfl

theorem continuous_coord (S T : HSp D) : Continuous (coord S T) :=
  (continuous_id.matrix_mul continuous_const).matrix_transpose

theorem continuous_coord_symm (S T : HSp D) : Continuous (coord S T).symm :=
  continuous_id.matrix_transpose.matrix_mul continuous_const

theorem coord_ratW (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    coord S T (ratW T S γ) = ratW S T (γ * S.gram⁻¹)ᵀ := by
  rw [coord_apply]
  unfold ratW
  rw [← Matrix.map_mul, Matrix.transpose_map]

theorem coord_symm_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    (coord S T).symm (ratW S T γ) = ratW T S (γᵀ * S.gram) := by
  rw [coord_symm_apply]
  unfold ratW
  rw [Matrix.map_mul, Matrix.transpose_map]

theorem coord_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (x : WO S T) (h : x.map φ = 0) :
    (coord S T x).map φ = 0 := by
  rw [coord_apply, Matrix.transpose_map, Matrix.map_mul, h, Matrix.zero_mul, Matrix.transpose_zero]

theorem coord_symm_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (y : WA S T) (h : y.map φ = 0) :
    ((coord S T).symm y).map φ = 0 := by
  rw [coord_symm_apply, Matrix.map_mul, Matrix.transpose_map, h, Matrix.transpose_zero, Matrix.zero_mul]

theorem symplOH_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    symplOH S T x y = symplH S T (coord S T x) (coord S T y) := by
  unfold symplOH symplH
  rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1 x y]
  rfl

theorem heisO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ) :
    heisO ψ S T w (fun x => f (coord S T x)) = fun x => Heisenberg₂ ψ S T (coord S T w) f (coord S T x) := by
  funext x
  simp only [heisO, Formalism.L2.Theta.Heisenberg₂, map_add, symplOH_eq S T hr]

theorem isThetaFunO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ) :
    IsThetaFunO ψ S T (fun x => f (coord S T x)) ↔ IsThetaFun ψ S T f := by
  have c1 := continuous_coord S T
  have c2 := continuous_coord_symm S T
  refine ⟨fun hf => ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩,
    fun hf => ⟨fun γ w => ?_, ?_, hf.cont.comp c1, fun k L hL h0 w => ?_⟩⟩
  · have := hf.quasi (γᵀ * S.gram) ((coord S T).symm w)
    rw [← coord_symm_ratW, symplOH_eq S T hr] at this
    simpa only [map_add, AddEquiv.apply_symm_apply] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).symm.toAddMonoidHom, hU.preimage c2, fun u hu h0 => ?_⟩
    have := hfix ((coord S T).symm u) hu (coord_symm_map_zero S T _ u h0)
    rw [heisO_coord S T hr] at this
    funext y
    simpa only [AddEquiv.apply_symm_apply] using congrFun this ((coord S T).symm y)
  · simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using hf.cont.comp c2
  · have := hf.smooth k ((coord S T).symm.toAddMonoidHom.comp L) (c2.comp hL)
      (fun t => coord_symm_map_zero S T _ _ (h0 t)) ((coord S T).symm w)
    simpa only [map_add, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] using this
  · have := hf.quasi (γ * S.gram⁻¹)ᵀ (coord S T w)
    rw [← coord_ratW, ← symplOH_eq S T hr] at this
    simpa only [map_add] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).toAddMonoidHom, hU.preimage c1, fun u hu h0 => ?_⟩
    rw [heisO_coord S T hr, hfix (coord S T u) hu (coord_map_zero S T _ u h0)]
  · have := hf.smooth k ((coord S T).toAddMonoidHom.comp L) (c1.comp hL)
      (fun t => coord_map_zero S T _ _ (h0 t)) (coord S T w)
    simpa only [map_add, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe] using this

theorem coord_gen (S T : HSp D) (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    coord S T (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * star (s i) * t j) := by
  rw [← AddEquiv.eq_symm_apply, coord_symm_apply]
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : incA D (S.gram k j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j := rfl
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem coord_mem_latVWS (S T : HSp D) (hr : S.rank ≤ T.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z)) : coord S T u ∈ latVWS S T Z := by
  have : latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) ≤ (latVWS S T Z).comap (coord S T).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, fun v hv => h0 v (not_not.2 hv), a, ha, s, hs, t, ht, ?_⟩
    simp only [if_pos hr]
    exact coord_gen S T _ a s t
  exact this hu

theorem exists_coord : ∀ (D : D7) (S T : HSp D), S.rank ≤ T.rank → ∃ e : WO S T ≃+ WA S T, Continuous e ∧ Continuous e.symm ∧ (∀ x, e x = toTWsmall S T x) ∧ (∀ x, e x ∈ ratL S T ↔ x ∈ ratL T S) ∧ (∀ (a : AE D) (x : WO S T), e (a • x) = a • e x) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ), heisO ψ S T w (fun x => f (e x)) = fun x => Heisenberg₂ ψ S T (e w) f (e x)) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ), IsThetaFunO ψ S T (fun x => f (e x)) ↔ IsThetaFun ψ S T f) ∧ ∀ (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T), u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) → e u ∈ latVWS S T Z := by
  intro D S T hr
  refine ⟨coord S T, continuous_coord S T, continuous_coord_symm S T, fun _ => rfl, fun x => ⟨?_, ?_⟩, fun a x => ?_,
    heisO_coord S T hr, isThetaFunO_coord S T hr, coord_mem_latVWS S T hr⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ratW S T γ = coord S T x := hγ
    refine ⟨γᵀ * S.gram, ?_⟩
    change ratW T S _ = x
    rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
  · rw [coord_apply, coord_apply, Matrix.smul_mul, Matrix.transpose_smul]

end GlobalTheory.OrientedCoord

end
