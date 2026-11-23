import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Cm

open Fb (Stab)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def ofCusp : cuspForms E a →ₗ[ℂ] Sm E a := Submodule.inclusion cuspForms_le_Sm

variable {E a}

@[simp] theorem coe_ofCusp (ψ : cuspForms E a) : (ofCusp E a ψ).1 = ψ.1 := rfl

theorem ofCusp_injective : Function.Injective (ofCusp E a) := Submodule.inclusion_injective _

theorem isCuspForm_ofCusp (ψ : cuspForms E a) : GlobalTheory.CuspRep.IsCuspForm (ofCusp E a ψ) := (isCuspForm_iff _).2 ψ.2

theorem mem_range_ofCusp {φ : Sm E a} : φ ∈ LinearMap.range (ofCusp E a) ↔ GlobalTheory.CuspRep.IsCuspForm φ :=
  ⟨fun ⟨ψ, h⟩ => h ▸ isCuspForm_ofCusp ψ, fun h => ⟨⟨φ.1, (isCuspForm_iff φ).1 h⟩, rfl⟩⟩

theorem ofCusp_uAction (u : UEnv E a) (ψ : cuspForms E a) :
    ofCusp E a (uActionCusp E a u ψ) = uTC E a u (ofCusp E a ψ) := rfl

theorem ofCusp_ρ (X : Lie E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).ρ (lieEq E a X) ψ) = act (.lie X) (ofCusp E a ψ) := by
  rw [gkModuleCusp_ρ_apply, ofCusp_uAction, uTC_ι]
  rfl

theorem ofCusp_σ (k : Kinf E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).σ (cptEq E a k) ψ) = act (.cpt k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofCusp_τ (k : GL (Fin a) (Af E)) (ψ : cuspForms E a) :
    ofCusp E a (finRepCusp E a k ψ) = act (.fin k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) Fb.finEmb_eq)

theorem exists_center_ofCusp {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ p ∈ (isExpLieAlgebra E a).centerU, ∃ q ∈ (isExpLieAlgebra E a).centerU, ∀ ψ : cuspForms E a,
      z (ofCusp E a ψ) = ofCusp E a (uActionCusp E a p ψ + Complex.I • uActionCusp E a q ψ) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_Zalg_iff.1 hz
  exact ⟨p, hp, q, hq, fun ψ => by rw [map_add, map_smul, ofCusp_uAction, ofCusp_uAction]; rfl⟩

theorem isStable_range : GlobalTheory.CuspRep.IsStable (LinearMap.range (ofCusp E a)) := by
  rintro o _ ⟨ψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, ofCusp_ρ X ψ⟩

theorem isCuspForm_act (o : Op E a) {φ : Sm E a} (h : GlobalTheory.CuspRep.IsCuspForm φ) : GlobalTheory.CuspRep.IsCuspForm (act o φ) :=
  mem_range_ofCusp.1 (isStable_range o φ (mem_range_ofCusp.2 h))

variable (E a) in

def ofAut : automorphicForms E a →ₗ[ℂ] Sm E a := Submodule.inclusion automorphicForms_le_Sm

@[simp] theorem coe_ofAut (ψ : automorphicForms E a) : (ofAut E a ψ).1 = ψ.1 := rfl

theorem ofAut_injective : Function.Injective (ofAut E a) := Submodule.inclusion_injective _

theorem mem_range_ofAut {φ : Sm E a} : φ ∈ LinearMap.range (ofAut E a) ↔ IsAutForm φ :=
  ⟨fun ⟨ψ, h⟩ => h ▸ (isAutForm_iff _).2 ψ.2, fun h => ⟨⟨φ.1, (isAutForm_iff φ).1 h⟩, rfl⟩⟩

variable (E a) in

def ofKZ : smoothKZ E a →ₗ[ℂ] Sm E a := (smEq E a).symm.toLinearMap ∘ₗ toArchSmooth

@[simp] theorem coe_ofKZ (ψ : smoothKZ E a) : (ofKZ E a ψ).1 = ψ.1 := rfl

theorem ofKZ_ρ (X : Lie E a) (ψ : smoothKZ E a) :
    ofKZ E a ((gkModule E a).ρ (lieEq E a X) ψ) = lie E a X (ofKZ E a ψ) := by
  rw [← uTC_ι]
  rfl

theorem ofKZ_σ (k : Kinf E a) (ψ : smoothKZ E a) :
    ofKZ E a ((gkModule E a).σ (cptEq E a k) ψ) = cptRep E a k (ofKZ E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofKZ_τ (k : GL (Fin a) (Af E)) (ψ : smoothKZ E a) :
    ofKZ E a (finRepKZ E a k ψ) = GlobalTheory.CuspRep.finRep E a k (ofKZ E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) Fb.finEmb_eq)

theorem isStable_map {U : Submodule ℂ (cuspForms E a)} (h : Stab U) : GlobalTheory.CuspRep.IsStable (U.map (ofCusp E a)) := by
  rintro o _ ⟨ψ, hψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, h.τ k ψ hψ, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, h.σ _ ψ hψ, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, h.ρ _ ψ hψ, ofCusp_ρ X ψ⟩

theorem stab_comap {V : Submodule ℂ (Sm E a)} (h : GlobalTheory.CuspRep.IsStable V) : Stab (V.comap (ofCusp E a)) := by
  refine ⟨fun X ψ hψ => ?_, fun k ψ hψ => ?_, fun k ψ hψ => ?_⟩
  · obtain ⟨X, rfl⟩ := (lieEq E a).surjective X
    rw [Submodule.mem_comap, ofCusp_ρ]
    exact h _ _ hψ
  · obtain ⟨k, rfl⟩ := (cptEq E a).surjective k
    rw [Submodule.mem_comap, ofCusp_σ]
    exact h _ _ hψ
  · rw [Submodule.mem_comap, ofCusp_τ]
    exact h _ _ hψ

def carrier (π : CuspSub E a) : Submodule ℂ (cuspForms E a) := π.V.comap (ofCusp E a)

theorem mem_carrier {π : CuspSub E a} {ψ : cuspForms E a} : ψ ∈ carrier π ↔ ofCusp E a ψ ∈ π.V := Iff.rfl

theorem map_carrier (π : CuspSub E a) : (carrier π).map (ofCusp E a) = π.V :=
  Submodule.map_comap_eq_self fun φ h => mem_range_ofCusp.2 (π.cusp φ h)

theorem stab_carrier (π : CuspSub E a) : Stab (carrier π) := stab_comap π.stable

abbrev toModule (π : CuspSub E a) : AdelicGKModule E a (carrier π) :=
  cuspSubmodule E a (carrier π) (stab_carrier π).ρ (stab_carrier π).σ (stab_carrier π).τ

theorem isIrreducible_toModule (π : CuspSub E a) : (toModule π).IsIrreducible := by
  refine (stab_carrier π).isIrreducible_iff.2 ⟨fun e => π.ne_bot (by rw [← map_carrier, e, Submodule.map_bot]),
    fun W hW hst => ?_⟩
  refine (π.irred _ ((Submodule.map_mono hW).trans (map_carrier π).le) (isStable_map hst)).imp (fun e => ?_) fun e => ?_
  · exact Submodule.map_injective_of_injective ofCusp_injective (e.trans (Submodule.map_bot _).symm)
  · exact Submodule.map_injective_of_injective ofCusp_injective (e.trans (map_carrier π).symm)

theorem isAdmissible_toModule (π : CuspSub E a) : (toModule π).IsAdmissible :=
  UnitaryAdmissible.isAdmissible_cuspSubmodule _ _ _ _ (isIrreducible_toModule π)

def carrierEq (π : CuspSub E a) : carrier π ≃ₗ[ℂ] π.V :=
  (Submodule.equivMapOfInjective _ ofCusp_injective _).trans (LinearEquiv.ofEq _ _ (map_carrier π))

@[simp] theorem coe_carrierEq (π : CuspSub E a) (ψ : carrier π) : (carrierEq π ψ).1 = ofCusp E a ψ.1 := rfl

theorem carrierEq_ρ (π : CuspSub E a) (X : Lie E a) (ψ : carrier π) :
    carrierEq π ((toModule π).gk.ρ (lieEq E a X) ψ) = π.op (.lie X) (carrierEq π ψ) := Subtype.ext (ofCusp_ρ X ψ.1)

theorem carrierEq_σ (π : CuspSub E a) (k : Kinf E a) (ψ : carrier π) :
    carrierEq π ((toModule π).gk.σ (cptEq E a k) ψ) = π.op (.cpt k) (carrierEq π ψ) := Subtype.ext (ofCusp_σ k ψ.1)

theorem carrierEq_τ (π : CuspSub E a) (k : GL (Fin a) (Af E)) (ψ : carrier π) :
    carrierEq π ((toModule π).τ k ψ) = π.op (.fin k) (carrierEq π ψ) := Subtype.ext (ofCusp_τ k ψ.1)

private theorem rep_comm {π π' : CuspSub E a} (T : carrier π →ₗ[ℂ] carrier π')
    (hρ : ∀ X ψ, T ((toModule π).gk.ρ X ψ) = (toModule π').gk.ρ X (T ψ))
    (hσ : ∀ k ψ, T ((toModule π).gk.σ k ψ) = (toModule π').gk.σ k (T ψ))
    (w : FreeMonoid ((isExpLieAlgebra E a).lieSubalgebra ⊕ archCompact E a)) (ψ : carrier π) :
    T ((toModule π).gk.rep w ψ) = (toModule π').gk.rep w (T ψ) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one]; rfl
  | of_mul x w ih =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← ih]
    rcases x with X | k
    · exact hρ X _
    · exact hσ k _

theorem iso_iff (π π' : CuspSub E a) :
    π.Iso π' ↔ Nonempty ((toModule π).fullRep.Equiv (toModule π').fullRep) := by
  constructor
  · rintro ⟨T, hT⟩
    let S : carrier π ≃ₗ[ℂ] carrier π' := ((carrierEq π).trans T).trans (carrierEq π').symm
    have hS : ∀ ψ, carrierEq π' (S ψ) = T (carrierEq π ψ) := fun ψ => (carrierEq π').apply_symm_apply _
    refine ⟨.mk S fun p => LinearMap.ext fun ψ => ?_⟩
    have hτ : S ((toModule π).τ p.2 ψ) = (toModule π').τ p.2 (S ψ) :=
      (carrierEq π').injective (by rw [hS, carrierEq_τ, carrierEq_τ, hT, hS])
    refine (rep_comm S.toLinearMap (fun X ψ => ?_) (fun k ψ => ?_) p.1 _).trans
      (congrArg ((toModule π').gk.rep p.1) hτ)
    · obtain ⟨X, rfl⟩ := (lieEq E a).surjective X
      exact (carrierEq π').injective (by rw [LinearEquiv.coe_coe, hS, carrierEq_ρ, carrierEq_ρ, hT, hS])
    · obtain ⟨k, rfl⟩ := (cptEq E a).surjective k
      exact (carrierEq π').injective (by rw [LinearEquiv.coe_coe, hS, carrierEq_σ, carrierEq_σ, hT, hS])
  · rintro ⟨e⟩
    have he : ∀ w g ψ, e.toLinearEquiv ((toModule π).gk.rep w ((toModule π).τ g ψ)) =
        (toModule π').gk.rep w ((toModule π').τ g (e.toLinearEquiv ψ)) := fun w g ψ =>
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (w, g) ψ
    refine ⟨((carrierEq π).symm.trans e.toLinearEquiv).trans (carrierEq π'), fun o φ => ?_⟩
    obtain ⟨ψ, rfl⟩ := (carrierEq π).surjective φ
    cases o with
    | fin k =>
      have := he 1 k ψ
      simp only [map_one, Module.End.one_apply] at this
      simp only [← carrierEq_τ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, this]
    | cpt k =>
      have := he (FreeMonoid.of (Sum.inr (cptEq E a k))) 1 ψ
      simp only [map_one, Module.End.one_apply] at this
      simp only [← carrierEq_σ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact congrArg _ this
    | lie X =>
      have := he (FreeMonoid.of (Sum.inl (lieEq E a X))) 1 ψ
      simp only [map_one, Module.End.one_apply] at this
      simp only [← carrierEq_ρ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact congrArg _ this

theorem mk_eq_mk_iff (π π' : CuspSub E a) :
    CG.mk π = CG.mk π' ↔ Nonempty ((toModule π).fullRep.Equiv (toModule π').fullRep) :=
  (Quotient.eq (r := CuspSub.setoid E a)).trans (iso_iff π π')

def ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi : (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible) :
    CuspSub E a where
  V := U.map (ofCusp E a)
  cusp := by rintro _ ⟨ψ, -, rfl⟩; exact isCuspForm_ofCusp ψ
  stable := isStable_map h
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

theorem ofIrr_carrier (π : CuspSub E a) : ofIrr _ (stab_carrier π) (isIrreducible_toModule π) = π :=
  CuspSub.ext (map_carrier π)

theorem centralZ_eq :
    UnitaryAdmissible.centralZ E a = UnitaryAdmissible.centralExp E a • lieEq E a (oneL E a) :=
  Subtype.ext (by rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← lieEq_oneL]; rfl)

theorem mem_centralCuspForms_of {ψ : cuspForms E a} (h : lie E a (oneL E a) (ofCusp E a ψ) = 0) :
    ψ ∈ centralCuspForms E a := fun s x => by
  have h1 : (gkModuleCusp E a).ρ (lieEq E a (oneL E a)) ψ = 0 :=
    ofCusp_injective ((ofCusp_ρ _ _).trans (h.trans (map_zero _).symm))
  have h2 : lieActionCusp E a (UnitaryAdmissible.centralZ E a) ψ = (0 : ℂ) • ψ := by
    rw [centralZ_eq, map_smul, zero_smul, LinearMap.smul_apply]
    exact (congrArg _ h1).trans (smul_zero _)
  rw [Reduction.centralSection_mul_comm, UnitaryAdmissible.apply_mul_centralSection h2 x s]
  simp

theorem lie_oneL_eq_zero {ψ : cuspForms E a} (h : ψ ∈ centralCuspForms E a) :
    lie E a (oneL E a) (ofCusp E a ψ) = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Subsingleton.elim (oneL E 0) 0, map_zero, LinearMap.zero_apply]
  · have h1 := ρ_centralZ_eq_zero h
    have h2 : UnitaryAdmissible.centralExp E a ≠ 0 :=
      inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne'))
    rw [centralZ_eq, map_smul, LinearMap.smul_apply, smul_eq_zero_iff_right h2] at h1
    exact (ofCusp_ρ _ ψ).symm.trans (by rw [h1, map_zero])

def toRep (π : CuspSub E a) (h : carrier π ≤ centralCuspForms E a) : CuspidalAutomorphicRepresentation E a :=
  .ofIrreducible (carrier π) h _ _ _ (isIrreducible_toModule π)

def ofRep (π : CuspidalAutomorphicRepresentation E a) : CuspSub E a :=
  ofIrr π.carrier ⟨π.stable_ρ, π.stable_σ, π.stable_τ⟩ π.isIrreducible

theorem carrier_toRep (π : CuspSub E a) (h) : (toRep π h).carrier = carrier π := rfl

theorem carrier_ofRep (π : CuspidalAutomorphicRepresentation E a) : carrier (ofRep π) = π.carrier :=
  carrier_ofIrr _ _ _

theorem ofRep_toRep (π : CuspSub E a) (h) : ofRep (toRep π h) = π := ofIrr_carrier π

theorem carrier_le_central (π : CuspSub E a) (h : ∀ φ ∈ π.V, lie E a (oneL E a) φ = 0) :
    carrier π ≤ centralCuspForms E a := fun _ hψ => mem_centralCuspForms_of (h _ hψ)

def trivRep (ha : a ≤ 1) : CuspidalAutomorphicRepresentation E a :=
  toRep (CuspSub.triv E ha) (carrier_le_central _ fun φ hφ => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    rw [map_smul, lie_oneFn, smul_zero])

end UpperTheory.V.Cm
