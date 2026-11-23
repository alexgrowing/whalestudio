import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Representation MulAction
open scoped TensorProduct

universe u

noncomputable section

section Restriction

variable {k G H V W : Type*} [CommRing k] [Group G] [Group H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] (ρ : Representation k G V)

theorem invariants_comp_eq_range (f : H →* G) :
    (Representation.invariants (ρ.comp f)) = (Representation.invariants (ρ.comp f.range.subtype)) := by
  ext x
  rw [mem_invariants, mem_invariants]
  constructor
  · rintro h ⟨_, y, rfl⟩
    exact h y
  · intro h y
    exact h ⟨f y, y, rfl⟩

theorem finrank_invariants_eq_of_linearEquiv {σ : Representation k G W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    Module.finrank k ρ.invariants = Module.finrank k σ.invariants := by
  have hmap : ρ.invariants.map (e : V →ₗ[k] W) = σ.invariants := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      change σ g (e v) = e v
      rw [← he, hv g]
    · intro hw
      refine ⟨e.symm w, fun g => e.injective ?_, e.apply_symm_apply w⟩
      rw [he, e.apply_symm_apply, hw g]
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem finrank_invariants_map_conj (K : Subgroup G) (g : G) :
    Module.finrank k (Representation.invariants (ρ.comp (K.map (MulAut.conj g).toMonoidHom).subtype)) =
      Module.finrank k (Representation.invariants (ρ.comp K.subtype)) := by
  have h1 : ∀ x ∈ (Representation.invariants (ρ.comp K.subtype)),
      ρ g x ∈ (Representation.invariants (ρ.comp (K.map (MulAut.conj g).toMonoidHom).subtype)) := by
    rintro x hx ⟨_, h, hh, rfl⟩
    have hx' : ρ h x = x := hx ⟨h, hh⟩
    change ρ (g * h * g⁻¹) (ρ g x) = ρ g x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hx']
  have h2 : ∀ y ∈ (Representation.invariants (ρ.comp (K.map (MulAut.conj g).toMonoidHom).subtype)),
      ρ g⁻¹ y ∈ (Representation.invariants (ρ.comp K.subtype)) := by
    rintro y hy ⟨h, hh⟩
    have hy' : ρ (g * h * g⁻¹) y = y := hy ⟨g * h * g⁻¹, h, hh, rfl⟩
    change ρ h (ρ g⁻¹ y) = ρ g⁻¹ y
    calc ρ h (ρ g⁻¹ y) = ρ (g⁻¹ * (g * h * g⁻¹)) y := by
          rw [show g⁻¹ * (g * h * g⁻¹) = h * g⁻¹ by group, map_mul, Module.End.mul_apply]
      _ = ρ g⁻¹ y := by rw [map_mul, Module.End.mul_apply, hy']
  let e : (Representation.invariants (ρ.comp K.subtype)) ≃ₗ[k]
      (Representation.invariants (ρ.comp (K.map (MulAut.conj g).toMonoidHom).subtype)) :=
    LinearEquiv.ofLinearMap ((ρ g).restrict h1) ((ρ g⁻¹).restrict h2)
      (by
        ext y
        change ρ g (ρ g⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (by
        ext x
        change ρ g⁻¹ (ρ g x) = x
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  exact e.finrank_eq.symm

theorem finrank_invariants_stabilizer_smul {X : Type*} [MulAction G X] (g : G) (x : X) :
    Module.finrank k (Representation.invariants (ρ.comp (MulAction.stabilizer G (g • x)).subtype)) =
      Module.finrank k (Representation.invariants (ρ.comp (MulAction.stabilizer G x).subtype)) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact finrank_invariants_map_conj ρ _ g

end Restriction

section Dual

variable {k G V : Type*} [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

theorem range_averageMap [Invertible (Fintype.card G : k)] :
    LinearMap.range ρ.averageMap = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ρ.averageMap_invariant v
  · intro v hv
    exact ⟨v, ρ.averageMap_id v hv⟩

theorem averageMap_apply [Invertible (Fintype.card G : k)] (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  simp [averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]

theorem averageMap_dual [Invertible (Fintype.card G : k)] :
    ρ.dual.averageMap = Module.Dual.transpose (R := k) ρ.averageMap := by
  ext f v
  rw [averageMap_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, averageMap_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp [Module.Dual.transpose_apply]

theorem finrank_dual_invariants [FiniteDimensional k V] (hG : (Fintype.card G : k) ≠ 0) :
    Module.finrank k ρ.dual.invariants = Module.finrank k ρ.invariants := by
  let _ := invertibleOfNonzero hG
  rw [← range_averageMap, ← range_averageMap, averageMap_dual]
  exact LinearMap.finrank_range_dualMap_eq_finrank_range _

end Dual

section Orbits

variable {k Γ X N : Type*} [Field k] [Group Γ] [MulAction Γ X] [AddCommGroup N] [Module k N]
  (σ : Representation k Γ N)

def equivariantFunctions : Submodule k (X → N) where
  carrier := {F | ∀ (g : Γ) (x : X), F (g • x) = σ g (F x)}
  zero_mem' g x := by simp
  add_mem' hF hG g x := by simp [hF g x, hG g x]
  smul_mem' c F hF g x := by simp [hF g x]

theorem exists_smul_eq_out (x : X) : ∃ m : Γ, m • x = (Quotient.mk (orbitRel Γ X) x).out :=
  Quotient.mk_out (s := orbitRel Γ X) x

def orbitMover (x : X) : Γ :=
  (Classical.choose (exists_smul_eq_out (Γ := Γ) x))⁻¹

theorem orbitMover_smul (x : X) : orbitMover (Γ := Γ) x • (Quotient.mk (orbitRel Γ X) x).out = x := by
  rw [orbitMover, inv_smul_eq_iff]
  exact (Classical.choose_spec (exists_smul_eq_out (Γ := Γ) x)).symm

theorem orbitRel_mk_smul (g : Γ) (x : X) :
    Quotient.mk (orbitRel Γ X) (g • x) = Quotient.mk (orbitRel Γ X) x :=
  Quotient.sound (mem_orbit x g)

theorem apply_out_mem_invariants {F : X → N} (hF : F ∈ equivariantFunctions (X := X) σ)
    (ω : orbitRel.Quotient Γ X) :
    F ω.out ∈ (Representation.invariants (σ.comp (MulAction.stabilizer Γ ω.out).subtype)) := fun h => by
  change σ h (F ω.out) = F ω.out
  rw [← hF, mem_stabilizer_iff.1 h.2]

def equivariantFunctionsToPi :
    equivariantFunctions (X := X) σ →ₗ[k]
      ∀ ω : orbitRel.Quotient Γ X, (Representation.invariants (σ.comp (MulAction.stabilizer Γ ω.out).subtype)) where
  toFun F ω := ⟨F.1 ω.out, apply_out_mem_invariants σ F.2 ω⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem equivariantFunctionsToPi_bijective :
    Function.Bijective (equivariantFunctionsToPi (X := X) σ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro F hF
    apply Subtype.ext
    funext x
    have h0 : F.1 (Quotient.mk (orbitRel Γ X) x).out = 0 :=
      congrArg Subtype.val (congrFun hF (Quotient.mk (orbitRel Γ X) x))
    change F.1 x = 0
    rw [← orbitMover_smul (Γ := Γ) x, F.2, h0, map_zero]
  · intro n
    let m : orbitRel.Quotient Γ X → N := fun ω => (n ω).1
    have hm : ∀ ω (h : Γ), h • ω.out = ω.out → σ h (m ω) = m ω := fun ω h hh =>
      (n ω).2 ⟨h, mem_stabilizer_iff.2 hh⟩
    let F : X → N := fun x => σ (orbitMover x) (m (Quotient.mk (orbitRel Γ X) x))
    have hF : F ∈ equivariantFunctions (X := X) σ := by
      intro g x
      set ω := Quotient.mk (orbitRel Γ X) x
      have h1 := orbitMover_smul (Γ := Γ) (g • x)
      rw [orbitRel_mk_smul] at h1
      have h2 := orbitMover_smul (Γ := Γ) x
      change σ (orbitMover (g • x)) (m (Quotient.mk (orbitRel Γ X) (g • x))) =
        σ g (σ (orbitMover x) (m ω))
      rw [orbitRel_mk_smul]
      have hstab : ((g * orbitMover x)⁻¹ * orbitMover (g • x)) • ω.out = ω.out := by
        rw [mul_smul, h1, mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
      calc σ (orbitMover (g • x)) (m ω)
          = σ (g * orbitMover x) (σ ((g * orbitMover x)⁻¹ * orbitMover (g • x)) (m ω)) := by
            rw [← Module.End.mul_apply (σ (g * orbitMover x)), ← map_mul, mul_inv_cancel_left]
        _ = σ (g * orbitMover x) (m ω) := by rw [hm ω _ hstab]
        _ = σ g (σ (orbitMover x) (m ω)) := by rw [map_mul, Module.End.mul_apply]
    refine ⟨⟨F, hF⟩, funext fun ω => Subtype.ext ?_⟩
    change σ (orbitMover ω.out) (m (Quotient.mk (orbitRel Γ X) ω.out)) = m ω
    have h3 := orbitMover_smul (Γ := Γ) ω.out
    have e : Quotient.mk (orbitRel Γ X) ω.out = ω := Quotient.out_eq ω
    rw [e] at h3 ⊢
    exact hm ω _ h3

def equivariantFunctionsEquivPi :
    equivariantFunctions (X := X) σ ≃ₗ[k]
      ∀ ω : orbitRel.Quotient Γ X, (Representation.invariants (σ.comp (MulAction.stabilizer Γ ω.out).subtype)) :=
  LinearEquiv.ofBijective _ (equivariantFunctionsToPi_bijective σ)

variable [Fintype X] [DecidableEq X]

def funTensorEquiv : (X → k) ⊗[k] N ≃ₗ[k] (X → N) :=
  (TensorProduct.comm k (X → k) N).trans (TensorProduct.piScalarRight k k N X)

theorem funTensorEquiv_tmul (f : X → k) (n : N) (x : X) :
    funTensorEquiv (f ⊗ₜ[k] n) x = f x • n := by
  simp [funTensorEquiv, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

theorem funTensorEquiv_tprod (g : Γ) (t : (X → k) ⊗[k] N) (x : X) :
    funTensorEquiv (((GroundTheory.Global.funPermRep k Γ X).tprod σ) g t) x =
      σ g (funTensorEquiv t (g⁻¹ • x)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f n =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, funTensorEquiv_tmul, funTensorEquiv_tmul,
      GroundTheory.Global.funPermRep_apply, map_smul]
  | add s t hs ht =>
    rw [map_add, map_add, Pi.add_apply, hs, ht, map_add, Pi.add_apply, map_add]

theorem map_invariants_funTensorEquiv :
    ((GroundTheory.Global.funPermRep k Γ X).tprod σ).invariants.map
        (funTensorEquiv (k := k) (X := X) (N := N) : (X → k) ⊗[k] N →ₗ[k] (X → N)) =
      equivariantFunctions (X := X) σ := by
  ext F
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩ g x
    have h := congrFun (congrArg funTensorEquiv (ht g)) (g • x)
    change funTensorEquiv t (g • x) = σ g (funTensorEquiv t x)
    rw [funTensorEquiv_tprod, inv_smul_smul] at h
    exact h.symm
  · intro hF
    refine ⟨funTensorEquiv.symm F, fun g => funTensorEquiv.injective ?_, funTensorEquiv.apply_symm_apply F⟩
    funext x
    rw [funTensorEquiv_tprod, LinearEquiv.apply_symm_apply, ← hF, smul_inv_smul]

theorem finrank_invariants_funPermRep_tprod [FiniteDimensional k N]
    [Fintype (orbitRel.Quotient Γ X)] :
    Module.finrank k ((GroundTheory.Global.funPermRep k Γ X).tprod σ).invariants =
      ∑ ω : orbitRel.Quotient Γ X, Module.finrank k (Representation.invariants (σ.comp (MulAction.stabilizer Γ ω.out).subtype)) := by
  rw [← LinearEquiv.finrank_map_eq (funTensorEquiv (k := k) (X := X) (N := N)), map_invariants_funTensorEquiv,
    (equivariantFunctionsEquivPi σ).finrank_eq, Module.finrank_pi_fintype]

end Orbits

section DualLine

variable {k G : Type u} [Field k] [Group G] (T M : Rep.{u} k G)

theorem eq_coord_smul_basis (b : Module.Basis (Fin 1) k T) (t : T) : t = b.coord 0 t • b 0 := by
  simpa using (b.sum_repr t).symm

theorem apply_eq_coord_smul (b : Module.Basis (Fin 1) k T) (A : T →ₗ[k] T) (t : T) :
    A t = b.coord 0 (A (b 0)) • t := by
  set c := b.coord 0 (A (b 0))
  have hA : A (b 0) = c • b 0 := eq_coord_smul_basis T b (A (b 0))
  calc A t = A (b.coord 0 t • b 0) := congrArg A (eq_coord_smul_basis T b t)
    _ = b.coord 0 t • (c • b 0) := by rw [map_smul, hA]
    _ = c • (b.coord 0 t • b 0) := smul_comm _ _ _
    _ = c • t := by rw [← eq_coord_smul_basis T b t]

variable (hT : Module.finrank k T = 1)

def lineBasis : Module.Basis (Fin 1) k T :=
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  Module.finBasisOfFinrankEq k T hT

def dualLineMap : (M →ₗ[k] T) →ₗ[k] Module.Dual k (T →ₗ[k] M) :=
  let b : Module.Basis (Fin 1) k T := lineBasis T hT
  LinearMap.mk₂ k (fun f n => b.coord 0 (f (n (b 0))))
    (fun f f' n => by simp) (fun c f n => by simp) (fun f n n' => by simp) (fun c f n => by simp)

theorem dualLineMap_apply (f : M →ₗ[k] T) (n : T →ₗ[k] M) :
    dualLineMap T M hT f n = (lineBasis T hT).coord 0 (f (n (lineBasis T hT 0))) :=
  rfl

theorem dualLineMap_comm (g : G) (f : M →ₗ[k] T) :
    dualLineMap T M hT ((dualRep T M).ρ g f) = (homRep T M).ρ.dual g (dualLineMap T M hT f) := by
  set b : Module.Basis (Fin 1) k T := lineBasis T hT
  set c := b.coord 0 (T.ρ g (b 0))
  have hc : ∀ t, T.ρ g t = c • t := fun t => apply_eq_coord_smul T b (T.ρ g) t
  ext n
  change b.coord 0 (T.ρ g (f (M.ρ g⁻¹ (n (b 0))))) =
    b.coord 0 (f (M.ρ g⁻¹ (n (T.ρ g⁻¹⁻¹ (b 0)))))
  rw [inv_inv, hc, hc (b 0)]
  simp only [map_smul]

theorem dualLineMap_injective : Function.Injective (dualLineMap T M hT) := by
  set b : Module.Basis (Fin 1) k T := lineBasis T hT
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext m
  have h0 := LinearMap.congr_fun hf ((b.coord 0).smulRight m)
  rw [dualLineMap_apply, LinearMap.smulRight_apply] at h0
  have h : b.repr (f m) 0 = 0 := by simpa [b] using h0
  rw [LinearMap.zero_apply, eq_coord_smul_basis T b (f m), Module.Basis.coord_apply, h, zero_smul]

def dualLineEquiv [Module.Finite k M] : (M →ₗ[k] T) ≃ₗ[k] Module.Dual k (T →ₗ[k] M) :=
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  LinearMap.linearEquivOfInjective (dualLineMap T M hT) (dualLineMap_injective T M hT) (by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap, Module.finrank_linearMap, hT, mul_one,
      one_mul])

theorem dualLineEquiv_comm [Module.Finite k M] (g : G) (f : M →ₗ[k] T) :
    dualLineEquiv T M hT ((dualRep T M).ρ g f) = (homRep T M).ρ.dual g (dualLineEquiv T M hT f) :=
  dualLineMap_comm T M hT g f

include hT in

theorem finrank_invariants_dualRep_comp [Module.Finite k M] (P : Subgroup G) [P.Normal]
    (hN : ∀ (g : P) (n : homRep T M), (homRep T M).ρ g n = n)
    {H : Type*} [Group H] (ψ : H →* G) [Fintype ((QuotientGroup.mk' P).comp ψ).range]
    (hD : (Fintype.card ((QuotientGroup.mk' P).comp ψ).range : k) ≠ 0) :
    Module.finrank k (Representation.invariants ((dualRep T M).ρ.comp ψ)) =
      Module.finrank k (Representation.invariants
        ((quotientRep P (homRep T M) hN).comp ((QuotientGroup.mk' P).comp ψ).range.subtype)) := by
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  have : Module.Finite k (T →ₗ[k] M) := inferInstance
  rw [finrank_invariants_eq_of_linearEquiv ((dualRep T M).ρ.comp ψ) (dualLineEquiv T M hT)
    (σ := ((homRep T M).ρ.dual).comp ψ) fun h f => dualLineEquiv_comm T M hT (ψ h) f]
  have e : ((homRep T M).ρ.dual).comp ψ =
      ((quotientRep P (homRep T M) hN).dual).comp ((QuotientGroup.mk' P).comp ψ) := rfl
  rw [e, invariants_comp_eq_range]
  exact finrank_dual_invariants ((quotientRep P (homRep T M) hN).comp
    ((QuotientGroup.mk' P).comp ψ).range.subtype) hD

end DualLine

end

end GroundTheory.ProfCoh
