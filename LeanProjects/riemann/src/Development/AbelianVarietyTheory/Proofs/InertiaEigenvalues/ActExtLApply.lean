import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

theorem actT_one' : actT L 1 = LinearMap.id := (latRep L).map_one

theorem actT_mul' (g h : G) : actT L (g * h) = actT L g ∘ₗ actT L h := (latRep L).map_mul g h

variable {L X χ₁ z}

theorem coc_one (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) : z 1 = 0 := by
  have h := hz.2 1 1
  simp only [mul_one, tableLineDegreeTwo.actTw, map_one, inv_one, Units.val_one, one_smul, actT_one', LinearMap.rTensor_id,
    LinearMap.id_apply] at h
  simpa using h

theorem actExtL_one (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) : actExtL L X χ₁ z 1 = LinearMap.id := by
  apply LinearMap.ext
  intro p
  rw [actExtL_apply]
  simp [tableLineDegreeTwo.actExt, coc_one hz, actT_one']

theorem actExtL_mul (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (g h : G) :
    actExtL L X χ₁ z (g * h) = actExtL L X χ₁ z g ∘ₗ actExtL L X χ₁ z h := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply, actExtL_apply, actExtL_apply, actExtL_apply]
  have hc := hz.2 g h
  simp only [tableLineDegreeTwo.actExt, hc, tableLineDegreeTwo.actTw, actT_mul', LinearMap.rTensor_comp, LinearMap.comp_apply, map_mul,
    Units.val_mul, map_add, map_smul, LinearMap.smul_apply]
  refine Prod.ext ?_ ?_
  · simp only [smul_add, smul_smul, add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    · congr 1
      have : ((χ₁ g : Oˣ) : O) * ((χ₁ g)⁻¹ : Oˣ) = 1 := Units.mul_inv _
      calc p.2 * (((χ₁ g : Oˣ) : O) * ((χ₁ h : Oˣ) : O) * (((χ₁ g)⁻¹ : Oˣ) : O))
          = p.2 * ((χ₁ h : Oˣ) : O) * (((χ₁ g : Oˣ) : O) * ((χ₁ g)⁻¹ : Oˣ)) := by ring
        _ = p.2 * ((χ₁ h : Oˣ) : O) := by rw [this, mul_one]
    · congr 1; ring
  · simp only
    ring

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def extRep (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) :
    Representation O G (((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) where
  toFun g := (tableLineDegreeTwo.kerExt L X lam a).mapQ _ (actExtL L X χ₁ z g) (actExtL_ker L X χ₁ z lam a hX g)
  map_one' := by
    apply Submodule.linearMap_qext
    ext p
    · simp [actExtL_one hz]
    · simp [actExtL_one hz]
  map_mul' g h := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro p
    simp [actExtL_mul hz, Module.End.mul_apply]

theorem extRep_mk (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G)
    (p : (↥L.T ⊗[O] X) × O) :
    extRep L X χ₁ z hz lam a hX g (Submodule.Quotient.mk p) = Submodule.Quotient.mk (tableLineDegreeTwo.actExt L X χ₁ z g p) := by
  rw [← actExtL_apply]; rfl

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
