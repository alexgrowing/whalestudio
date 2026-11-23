import Mathlib
import GroundTheory.ProfiniteCohomology.DiscreteModules
import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply

namespace GroundTheory.ProfCoh

open IntermediateField

universe w u

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

section Topology

variable (K L)

theorem galois_compactSpace [IsGalois K L] : CompactSpace Gal(L/K) :=
  inferInstance

theorem galois_t2Space [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  inferInstance

theorem galois_isProfinite [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Topology

section Open

theorem apply_eq_of_mem_fixingSubgroup_adjoin {x : L} {σ : Gal(L/K)}
    (hσ : σ ∈ (K⟮x⟯).fixingSubgroup) : σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (mem_adjoin_simple_self K x)

theorem isOpen_of_forall_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K)) (x : L)
    (h : ∀ σ : Gal(L/K), σ x = x → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ))
    (fixingSubgroup_isOpen K⟮x⟯)

end Open

section Discrete

variable [Algebra.IsIntegral K L]

instance isDiscreteRep_galAdd : IsDiscreteRep (galAdd K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galAddInt : IsDiscreteRep (galAddInt.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galAddZ : IsDiscreteRep (galAddZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galUnits : IsDiscreteRep (galUnits.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnits_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galUnitsZ : IsDiscreteRep (galUnitsZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnitsZ_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galRootsOfUnity (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{w} K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnity_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩

instance isDiscreteRep_galRootsOfUnityZ (n : ℕ) : IsDiscreteRep (galRootsOfUnityZ K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnityZ_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩

end Discrete

section Galois

variable (K L) [IsGalois K L]

example : IsDiscreteRep (galUnits.{u} K L) := inferInstance
example (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{u} K L n) := inferInstance
example : IsDiscreteRep (galAdd K L) := inferInstance

end Galois

end GroundTheory.ProfCoh
