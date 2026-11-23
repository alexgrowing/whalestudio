import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def intO : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

def Xq (lam : O) (a : ℕ) : Submodule O (LL ⧸ intO (O := O) LL) :=
  LinearMap.ker (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] (LL ⧸ intO (O := O) LL)))

variable {LL}
variable {V V' : Type} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module LL V'] [Module O V']
  [IsScalarTower O LL V']

def scalQ (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') (t : ↥T) :
    (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  (intO (O := O) LL).liftQ (T'.mkQ ∘ₗ (LinearMap.id : LL →ₗ[O] LL).smulRight (j t)) (by
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.linearMap_apply, algebraMap_smul]
    exact T'.smul_mem c (hj t t.2))

def scalB (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T →ₗ[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' where
  toFun := scalQ T T' j hj
  map_add' t u := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_add]
  map_smul' c t := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_comm s c]

def iotaG (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T ⊗[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  TensorProduct.lift (scalB T T' j hj)

theorem iotaG_tmul (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T')
    (t : ↥T) (s : LL) :
    iotaG T T' j hj (t ⊗ₜ Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • j t) := rfl

end Gen

section Conc

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def iotaW (lam : O) (a k : ℕ) :
    ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ stdG O LL k :=
  iotaG (stdG O LL k) (stdG O LL k) LinearMap.id (fun _ h => h) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

def constOne : LL →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => LinearMap.id

theorem constOne_mem : ∀ v ∈ intO (O := O) LL, constOne (O := O) LL v ∈ stdG O LL 1 := by
  rintro _ ⟨c, rfl⟩
  simp only [constOne, stdG]
  refine ⟨fun _ => c, ?_⟩
  ext i
  simp

def iotaC (lam : O) (a : ℕ) :
    ↥(intO (O := O) LL) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin 1 → LL) ⧸ stdG O LL 1 :=
  iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

variable {LL}

def latOne (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) :
    Lattice (O := O) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ)) where
  T := intO LL
  stable g x hx := by
    obtain ⟨c, rfl⟩ := hx
    refine ⟨((ψ g : Oˣ) : O) * c, ?_⟩
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.linearMap_apply, Algebra.smul_def]
  fg := by
    rw [intO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL ((intO (O := O) LL : Set LL)) :=
      Submodule.subset_span ⟨1, map_one (algebraMap O LL)⟩
    simpa using Submodule.smul_mem _ x h1

end Conc

end GlobalTheory.UseLoc.Cases

end
