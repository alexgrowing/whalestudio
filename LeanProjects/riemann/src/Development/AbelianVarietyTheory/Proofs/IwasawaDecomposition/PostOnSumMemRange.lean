import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLift

theorem exists_factor {U H X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (f : U →ₗ[ℂ] X)
    (hf : ∀ x, f x ∈ LinearMap.range e) : ∃ g : U →ₗ[ℂ] H, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x => ?_⟩
  have h := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict _ hf x)
  exact congrArg Subtype.val h

theorem postOn_sum_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ g, c g • L g) T = ∑ g, c g • postOn M (L g) T := by
  ext v h
  simp [postOn_apply, LinearMap.sum_apply]

theorem postOn_sum_mem_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    {H : Type} [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] MMap M)
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (a : G → H →ₗ[ℂ] H)
    (ha : ∀ g y, e (a g y) = postOn M (L g) (e y)) {T : MMap M} (hT : T ∈ LinearMap.range e) :
    postOn M (∑ g, c g • L g) T ∈ LinearMap.range e := by
  obtain ⟨y, rfl⟩ := hT
  refine ⟨∑ g, c g • a g y, ?_⟩
  rw [postOn_sum_smul, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, ha]

theorem is_inj {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : Function.Injective M.e := h.1

theorem is_range {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : LinearMap.range M.e = V := h.2.1

theorem exists_factor_hmod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {G : Type} [Fintype G]
    {U : Type} [AddCommGroup U] [Module ℂ U] {H : HMod (MMap M)} {W : Submodule ℂ (MMap M)}
    {ip : MMap M → MMap M → ℂ} (hH : H.Is W ip)
    (c : G → ℂ) {L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {a : G → H.H →ₗ[ℂ] H.H}
    (ha : ∀ g y, H.e (a g y) = postOn M (L g) (H.e y)) (f : U →ₗ[ℂ] MMap M) (hf : ∀ x, f x ∈ W) :
    ∃ th : U →ₗ[ℂ] H.H, ∀ x, H.e (th x) = postOn M (∑ g, c g • L g) (f x) :=
  exists_factor _ (is_inj hH) (postOn M (∑ g, c g • L g) ∘ₗ f) fun x =>
    postOn_sum_mem_range M H.e c L a ha (by rw [is_range hH]; exact hf x)

set_option maxHeartbeats 1000000 in

theorem exists_thG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_thF_mem → ∃ th, ({ R with thG := th } : RealDat D A Ks).thP_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ _ hM hF
  have key : ∀ i t, ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H,
      ∀ x, (R.HW i (sg0 D A)).e (th x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x) := fun i t =>
    exists_factor_hmod (hM.HW i (sg0 D A)) (RealDat.eC (A := A) (sg0 D A)) (hM.gW i (sg0 D A)) (R.thF i t) (hF i t)
  choose th hth using key
  exact ⟨th, hth⟩

end GlobalTheory.GoodProjLift
