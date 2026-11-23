import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem exact_of_finrank_add {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (h0 : p ∘ₗ f = 0)
    (hd : Module.finrank K V = Module.finrank K U + Module.finrank K W) : Function.Exact f p := by
  rw [LinearMap.exact_iff]
  have hle : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hrn
  have hrf := LinearMap.finrank_range_of_inj hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem finrank_add_of_exact {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (he : Function.Exact f p) :
    Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  rw [LinearMap.exact_iff] at he
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [he, LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.finrank_range_of_inj hf] at hrn
  omega

theorem DFun.map_exact_middle {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hB : F.Obj B) (hf : IsHom A B f) (hp : IsHom B C p)
    (hi : Function.Injective f) (hs : Function.Surjective p) (he : Function.Exact f p) (i : ZMod n) :
    Function.Exact (F.map A B f i) (F.map B C p i) := by
  have hA : F.Obj A := F.obj_sub A B f hf hi hB
  have hC : F.Obj C := F.obj_quot B C p hp hs hB
  have hd := finrank_add_of_exact f p hi hs he
  simp only [Module.finrank_fin_fun] at hd
  have hpf : p ∘ₗ f = 0 := LinearMap.ext fun x => he.apply_apply_eq_zero x
  have h0hom : IsHom A C (0 : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) := fun g x => by simp
  have hcomp : F.map B C p i ∘ₗ F.map A B f i = 0 := by
    rw [← F.map_comp A B C f p hA hB hC hf hp i, hpf]
    refine LinearMap.ext fun x => ?_
    have h := F.map_smul A C 0 0 hA hC h0hom i x
    simpa using h
  refine exact_of_finrank_add (F.map A B f i) (F.map B C p i) (F.map_inj A B f hA hB hf hi i)
    (F.map_surj B C p hB hC hp hs i) hcomp ?_
  simp only [Vc, Module.finrank_fin_fun]
  exact hd

end GlobalTheory.Models
