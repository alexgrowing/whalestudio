import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

def ofCusp : cuspForms E a →ₗ[ℂ] TR.Sm E a := Submodule.inclusion cuspForms_le_Sm

variable {E a}

@[simp] theorem coe_ofCusp (ψ : cuspForms E a) : (ofCusp E a ψ).1 = ψ.1 := rfl

theorem ofCusp_injective : Function.Injective (ofCusp E a) := Submodule.inclusion_injective _

theorem isCuspForm_ofCusp (ψ : cuspForms E a) : TR.IsCuspForm (ofCusp E a ψ) := (isCuspForm_iff _).2 ψ.2

theorem mem_range_ofCusp {φ : TR.Sm E a} : φ ∈ LinearMap.range (ofCusp E a) ↔ TR.IsCuspForm φ :=
  ⟨fun ⟨ψ, h⟩ => h ▸ isCuspForm_ofCusp ψ, fun h => ⟨⟨φ.1, (isCuspForm_iff φ).1 h⟩, rfl⟩⟩

theorem ofCusp_uAction (u : UEnv E a) (ψ : cuspForms E a) :
    ofCusp E a (uActionCusp E a u ψ) = uTR E a u (ofCusp E a ψ) := rfl

theorem ofCusp_ρ (X : TR.Lie E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).ρ (lieEq E a X) ψ) = TR.act (.lie X) (ofCusp E a ψ) := by
  rw [gkModuleCusp_ρ_apply, ofCusp_uAction, uTR_ι]
  rfl

theorem ofCusp_σ (k : TR.Kinf E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).σ (cptEq E a k) ψ) = TR.act (.cpt k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofCusp_τ (k : GL (Fin a) (Af E)) (ψ : cuspForms E a) :
    ofCusp E a (finRepCusp E a k ψ) = TR.act (.fin k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) finEmb_eq)

theorem isStable_range : TR.IsStable (LinearMap.range (ofCusp E a)) := by
  rintro o _ ⟨ψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, ofCusp_ρ X ψ⟩

theorem isCuspForm_act (o : TR.Op E a) {φ : TR.Sm E a} (h : TR.IsCuspForm φ) : TR.IsCuspForm (TR.act o φ) :=
  mem_range_ofCusp.1 (isStable_range o φ (mem_range_ofCusp.2 h))

variable (E a) in

def ofKZ : smoothKZ E a →ₗ[ℂ] TR.Sm E a := (smEq E a).symm.toLinearMap ∘ₗ toArchSmooth

@[simp] theorem coe_ofKZ (ψ : smoothKZ E a) : (ofKZ E a ψ).1 = ψ.1 := rfl

theorem ofKZ_ρ (X : TR.Lie E a) (ψ : smoothKZ E a) :
    ofKZ E a ((gkModule E a).ρ (lieEq E a X) ψ) = TR.lie E a X (ofKZ E a ψ) := by
  rw [← uTR_ι]
  rfl

theorem ofKZ_σ (k : TR.Kinf E a) (ψ : smoothKZ E a) :
    ofKZ E a ((gkModule E a).σ (cptEq E a k) ψ) = TR.cptRep E a k (ofKZ E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofKZ_τ (k : GL (Fin a) (Af E)) (ψ : smoothKZ E a) :
    ofKZ E a (finRepKZ E a k ψ) = TR.finRep E a k (ofKZ E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) finEmb_eq)

omit [IsTotallyReal E] in

structure Stab (U : Submodule ℂ (cuspForms E a)) : Prop where
  ρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp E a).ρ X φ ∈ U
  σ : ∀ k, ∀ φ ∈ U, (gkModuleCusp E a).σ k φ ∈ U
  τ : ∀ g, ∀ φ ∈ U, finRepCusp E a g φ ∈ U

omit [IsTotallyReal E] in
theorem stab_central : Stab (centralCuspForms E a) :=
  ⟨fun X _ h => ρ_mem_centralCuspForms X h, fun k _ h => σ_mem_centralCuspForms k h,
    fun g _ h => finRepCusp_mem_centralCuspForms g h⟩

theorem Stab.map {U : Submodule ℂ (cuspForms E a)} (h : Stab U) : TR.IsStable (U.map (ofCusp E a)) := by
  rintro o _ ⟨ψ, hψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, h.τ k ψ hψ, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, h.σ _ ψ hψ, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, h.ρ _ ψ hψ, ofCusp_ρ X ψ⟩

theorem stab_comap {V : Submodule ℂ (TR.Sm E a)} (h : TR.IsStable V) : Stab (V.comap (ofCusp E a)) := by
  refine ⟨fun X ψ hψ => ?_, fun k ψ hψ => ?_, fun k ψ hψ => ?_⟩
  · obtain ⟨X, rfl⟩ := (lieEq E a).surjective X
    rw [Submodule.mem_comap, ofCusp_ρ]
    exact h _ _ hψ
  · obtain ⟨k, rfl⟩ := (cptEq E a).surjective k
    rw [Submodule.mem_comap, ofCusp_σ]
    exact h _ _ hψ
  · rw [Submodule.mem_comap, ofCusp_τ]
    exact h _ _ hψ

omit [IsTotallyReal E] in

theorem Stab.isIrreducible_iff {U : Submodule ℂ (cuspForms E a)} (h : Stab U) :
    (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible ↔ U ≠ ⊥ ∧ ∀ W ≤ U, Stab W → W = ⊥ ∨ W = U := by
  refine ⟨fun hi => ?_, fun hi => isIrreducible_cuspSubmodule_of U h.ρ h.σ h.τ hi.1
    fun W hW h1 h2 h3 => hi.2 W hW ⟨h1, h2, h3⟩⟩
  set M := cuspSubmodule E a U h.ρ h.σ h.τ
  have hs : IsSimpleOrder (Subrepresentation M.fullRep) := hi
  refine ⟨fun e => ?_, fun W hW hst => ?_⟩
  · have : Subsingleton U := by rw [e]; infer_instance
    exact bot_ne_top (α := Subrepresentation M.fullRep)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  · have h1 : ∀ (w : FreeMonoid ((isExpLieAlgebra E a).lieSubalgebra ⊕ archCompact E a)) (y : U),
        y.1 ∈ W → (M.gk.rep w y).1 ∈ W := fun w => by
      induction w using FreeMonoid.inductionOn' with
      | one => intro y hy; rwa [map_one]
      | of_mul x w ih =>
        intro y hy
        rw [map_mul, Module.End.mul_apply]
        rcases x with X | k
        · exact hst.ρ X _ (ih y hy)
        · exact hst.σ k _ (ih y hy)
    let Y : Subrepresentation M.fullRep := ⟨W.comap U.subtype, fun p y hy => h1 p.1 _ (hst.τ p.2 _ hy)⟩
    have e : (W.comap U.subtype).map U.subtype = W := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hW]
    rcases eq_bot_or_eq_top Y with h0 | h0
    · left
      rw [← e, show W.comap U.subtype = ⊥ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_bot]
    · right
      rw [← e, show W.comap U.subtype = ⊤ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_subtype_top]

def carrier (π : TR.CuspSub E a) : Submodule ℂ (cuspForms E a) := π.V.comap (ofCusp E a)

theorem mem_carrier {π : TR.CuspSub E a} {ψ : cuspForms E a} : ψ ∈ carrier π ↔ ofCusp E a ψ ∈ π.V := Iff.rfl

theorem map_carrier (π : TR.CuspSub E a) : (carrier π).map (ofCusp E a) = π.V :=
  Submodule.map_comap_eq_self fun φ h => mem_range_ofCusp.2 (π.cusp φ h)

theorem stab_carrier (π : TR.CuspSub E a) : Stab (carrier π) := stab_comap π.stable

abbrev toModule (π : TR.CuspSub E a) : AdelicGKModule E a (carrier π) :=
  cuspSubmodule E a (carrier π) (stab_carrier π).ρ (stab_carrier π).σ (stab_carrier π).τ

theorem isIrreducible_toModule (π : TR.CuspSub E a) : (toModule π).IsIrreducible := by
  refine (stab_carrier π).isIrreducible_iff.2 ⟨fun e => π.ne_bot (by rw [← map_carrier, e, Submodule.map_bot]),
    fun W hW hst => ?_⟩
  refine (π.irred _ ((Submodule.map_mono hW).trans (map_carrier π).le) hst.map).imp (fun e => ?_) fun e => ?_
  · exact Submodule.map_injective_of_injective ofCusp_injective (e.trans (Submodule.map_bot _).symm)
  · exact Submodule.map_injective_of_injective ofCusp_injective (e.trans (map_carrier π).symm)

theorem isAdmissible_toModule (π : TR.CuspSub E a) : (toModule π).IsAdmissible :=
  UnitaryAdmissible.isAdmissible_cuspSubmodule _ _ _ _ (isIrreducible_toModule π)

def carrierEq (π : TR.CuspSub E a) : carrier π ≃ₗ[ℂ] π.V :=
  (Submodule.equivMapOfInjective _ ofCusp_injective _).trans (LinearEquiv.ofEq _ _ (map_carrier π))

@[simp] theorem coe_carrierEq (π : TR.CuspSub E a) (ψ : carrier π) : (carrierEq π ψ).1 = ofCusp E a ψ.1 := rfl

theorem carrierEq_ρ (π : TR.CuspSub E a) (X : TR.Lie E a) (ψ : carrier π) :
    carrierEq π ((toModule π).gk.ρ (lieEq E a X) ψ) = π.op (.lie X) (carrierEq π ψ) := Subtype.ext (ofCusp_ρ X ψ.1)

theorem carrierEq_σ (π : TR.CuspSub E a) (k : TR.Kinf E a) (ψ : carrier π) :
    carrierEq π ((toModule π).gk.σ (cptEq E a k) ψ) = π.op (.cpt k) (carrierEq π ψ) := Subtype.ext (ofCusp_σ k ψ.1)

theorem carrierEq_τ (π : TR.CuspSub E a) (k : GL (Fin a) (Af E)) (ψ : carrier π) :
    carrierEq π ((toModule π).τ k ψ) = π.op (.fin k) (carrierEq π ψ) := Subtype.ext (ofCusp_τ k ψ.1)

def ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi : (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible) :
    TR.CuspSub E a where
  V := U.map (ofCusp E a)
  cusp := by rintro _ ⟨ψ, -, rfl⟩; exact isCuspForm_ofCusp ψ
  stable := h.map
  ne_bot e := (h.isIrreducible_iff.1 hi).1
    (Submodule.map_injective_of_injective ofCusp_injective (e.trans (Submodule.map_bot _).symm))
  irred W hW hst := by
    have e : (W.comap (ofCusp E a)).map (ofCusp E a) = W :=
      Submodule.map_comap_eq_self (hW.trans LinearMap.map_le_range)
    refine ((h.isIrreducible_iff.1 hi).2 _ ((Submodule.comap_mono hW).trans
      (Submodule.comap_map_eq_of_injective ofCusp_injective U).le) (stab_comap hst)).imp (fun e' => ?_) fun e' => ?_
    · rw [← e, e', Submodule.map_bot]
    · rw [← e, e']

theorem carrier_ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi) : carrier (ofIrr U h hi) = U :=
  Submodule.comap_map_eq_of_injective ofCusp_injective U

theorem ofIrr_carrier (π : TR.CuspSub E a) : ofIrr _ (stab_carrier π) (isIrreducible_toModule π) = π :=
  TR.CuspSub.ext (map_carrier π)

theorem centralZ_eq :
    UnitaryAdmissible.centralZ E a = UnitaryAdmissible.centralExp E a • lieEq E a (TR.oneL E a) :=
  Subtype.ext (by rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← lieEq_oneL]; rfl)

theorem mem_centralCuspForms_of {ψ : cuspForms E a} (h : TR.lie E a (TR.oneL E a) (ofCusp E a ψ) = 0) :
    ψ ∈ centralCuspForms E a := fun s x => by
  have h1 : (gkModuleCusp E a).ρ (lieEq E a (TR.oneL E a)) ψ = 0 :=
    ofCusp_injective ((ofCusp_ρ _ _).trans (h.trans (map_zero _).symm))
  have h2 : lieActionCusp E a (UnitaryAdmissible.centralZ E a) ψ = (0 : ℂ) • ψ := by
    rw [centralZ_eq, map_smul, zero_smul, LinearMap.smul_apply]
    exact (congrArg _ h1).trans (smul_zero _)
  rw [Reduction.centralSection_mul_comm, UnitaryAdmissible.apply_mul_centralSection h2 x s]
  simp

def toRep (π : TR.CuspSub E a) (h : carrier π ≤ centralCuspForms E a) : CuspidalAutomorphicRepresentation E a :=
  .ofIrreducible (carrier π) h _ _ _ (isIrreducible_toModule π)

def ofRep (π : CuspidalAutomorphicRepresentation E a) : TR.CuspSub E a :=
  ofIrr π.carrier ⟨π.stable_ρ, π.stable_σ, π.stable_τ⟩ π.isIrreducible

theorem carrier_le_central (π : TR.CuspSub E a) (h : ∀ φ ∈ π.V, TR.lie E a (TR.oneL E a) φ = 0) :
    carrier π ≤ centralCuspForms E a := fun _ hψ => mem_centralCuspForms_of (h _ hψ)

def trivRep (ha : a ≤ 1) : CuspidalAutomorphicRepresentation E a :=
  toRep (TR.CuspSub.triv E ha) (carrier_le_central _ fun φ hφ => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    rw [map_smul, TR.lie_oneFn, smul_zero])

end UpperTheory.V.Fb
