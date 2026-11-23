import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem senle_exists_coker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (C : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom B C q ∧ Function.Surjective q ∧ Function.Exact j q := by
  have hle : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (B.ρ g) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A.ρ g x, hj g x⟩
  obtain ⟨C, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) hle)
  refine ⟨C, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => ?_,
    e.surjective.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    rfl
  · simp [Submodule.Quotient.mk_eq_zero]

theorem senle_exists_ker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (C : Ob k G) (s : (Fin C.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom C A s ∧ Function.Injective s ∧ Function.Exact s p := by
  have hle : ∀ g, LinearMap.ker p ≤ (LinearMap.ker p).comap (A.ρ g) := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker]
    rw [hp g x, hx, map_zero]
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) hle)
  refine ⟨C, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (Submodule.injective_subtype _).comp e.symm.injective, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, e.symm_apply_apply, e.symm_apply_apply]
    rfl
  · constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem sen_push_pre_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  intro k G _ _ l n _ _ _ R F B A₁ A j p w w' N hB hj hji hp hps hN i x
  have hA₁ : F.Obj A₁ := F.obj_sub A₁ B j hj hji hB
  obtain ⟨C, q, hq, hqs, hex⟩ := senle_exists_coker A₁ B j hj
  obtain ⟨K, s, hs, hsi, hex'⟩ := senle_exists_ker A₁ A p hp
  have h1 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B C j q N hB hj hq hji hqs hex i (hN.1 i) (hN.2.2 i) x
  have hsat := GlobalTheory.PhiGam.Sat.main R (F.D B) (F.D A₁) (F.map A₁ B j) (F.map_inj A₁ B j hA₁ hB hj hji)
    (F.map_φ A₁ B j hA₁ hB hj) (F.map_γ A₁ B j hA₁ hB hj) w w' N hN.1 hN.2.1 hN.2.2
  have h2 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ A s p (F.pre A₁ B j N) hA₁ hs hp hsi hps hex' i (hsat.1 i) (hsat.2.2 i) x
  omega

end GlobalTheory.Models
