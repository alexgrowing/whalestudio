import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HatIntSmul

theorem mem_stdLat_coord {E : Type} [Field E] [NumberField E] {n : ℕ} {s : Fin n → E}
    (hs : s ∈ Formalism.L2.Pj.stdLat E n) (j : Fin n) : ∃ o : 𝓞 E, s j = (o : E) := by
  have := (Submodule.mem_pi.mp hs) j (Set.mem_univ _)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp this
  exact ⟨o, ho.symm⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (i : Fin n) (o : 𝓞 E) :
    Pi.single i (o : E) ∈ Formalism.L2.Pj.stdLat E n := by
  refine Submodule.mem_pi.mpr fun j _ => ?_
  rw [Submodule.mem_one]
  by_cases h : j = i
  · subst h; exact ⟨o, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem nsmul_tmul {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
    (a : ℕ) (β : Af F) (x : E) : a • (β ⊗ₜ[F] x) = β ⊗ₜ[F] (((a : 𝓞 E) : E) * x) := by
  have h := map_nsmul (TensorProduct.mk F (Af F) E β) a x
  simp only [TensorProduct.mk_apply] at h
  rw [← h, nsmul_eq_mul]
  simp

set_option maxHeartbeats 2000000 in

theorem sq_smul_mulVec_mem_hat : ∀ (D : D7) (n : ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a : ℕ), (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n) → ∀ (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), (∀ i j, M i j ∈ intAE D) → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)), (a ^ 2) • (M *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  intro D n Λ a h1 h2 M hM y hy
  have mulMem : ∀ {x y : Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
    intro x y hx hy
    refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
    · intro x _; rw [zero_mul]; exact zero_mem _
    · intro x _; rw [mul_zero]; exact zero_mem _
    · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
    · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
    · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
    · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

  have stepA : ∀ w : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, w i ∈ intAE D) →
      a • w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    intro w hw
    have hw' : a • w = ∑ i, a • Pi.single i (w i) := by
      rw [← Finset.smul_sum, Finset.univ_sum_single]
    rw [hw']
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, a • Pi.single i z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, o, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨β, fun v => hβ v, (a : 𝓞 D.host.E) • Pi.single i (o : D.host.E), h1 _ (single_mem_stdLat i o), ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_tmul, Algebra.smul_def]
        · simp [Pi.single_apply, hk]
      | zero => simp
      | add x y _ _ hx hy => rw [Pi.single_add, smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Pi.single_neg, smul_neg]; exact neg_mem hx
    exact key _ (hw i)
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Classical.axiomOfChoice (mem_stdLat_coord (h2 x hx))
    have e : (a ^ 2) • (M *ᵥ fun i => α ⊗ₜ[D.host.F] x i) =
        a • (M *ᵥ fun j => α ⊗ₜ[D.host.F] ((o j : 𝓞 D.host.E) : D.host.E)) := by
      rw [pow_two, mul_smul, ← Matrix.mulVec_smul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_tmul, ← ho j]
      simp [Algebra.smul_def]
    rw [e]
    refine stepA _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => mulMem (hM i j) (AddSubgroup.subset_closure ⟨α, fun v => hα v, o j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hy

end GlobalTheory.HatIntSmul
