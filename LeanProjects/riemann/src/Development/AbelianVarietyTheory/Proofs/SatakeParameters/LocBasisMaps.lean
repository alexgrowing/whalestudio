import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.YYMaps

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

theorem natsmul_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    (L : Submodule (𝓞 D.host.E) V) (s : ℕ) {y : V} (hy : y ∈ L) : (s : D.host.E) • y ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy s

theorem homL_maps {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') : ∀ x ∈ L, A *ᵥ x ∈ L' := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; simp
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem c (hA x hx)

theorem yy_maps
    (hA0 : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ TaylorLogMetric.YYl D L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L' := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨s, hs, t, ht⟩ := hA0 a ha
    refine ⟨s, hs, fun x hx => ?_⟩
    have e : (s : D.host.E) • ((a • A) *ᵥ x) = t • (A *ᵥ x) := by
      rw [Matrix.smul_mulVec, smul_smul, ← ht, algebraMap_smul]
    rw [e]
    exact L'.smul_mem t (homL_maps D hA x hx)
  | zero => exact ⟨1, Nat.coprime_one_left p, fun x _ => by simp⟩
  | add B C _ _ hB hC =>
    obtain ⟨s, hs, hB⟩ := hB
    obtain ⟨t, ht, hC⟩ := hC
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun x hx => ?_⟩
    have e : ((s * t : ℕ) : D.host.E) • ((B + C) *ᵥ x) =
        (t : D.host.E) • ((s : D.host.E) • (B *ᵥ x)) + (s : D.host.E) • ((t : D.host.E) • (C *ᵥ x)) := by
      rw [Matrix.add_mulVec, smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : D.host.E) (s : D.host.E)]
    rw [e]
    exact L'.add_mem (natsmul_mem D L' t (hB x hx)) (natsmul_mem D L' s (hC x hx))
  | smul c B _ hB =>
    obtain ⟨s, hs, hB⟩ := hB
    refine ⟨s, hs, fun x hx => ?_⟩
    rw [Matrix.smul_mulVec, smul_comm]
    exact L'.smul_mem c (hB x hx)

end Glob

theorem locBasis_maps : ∀ (D : D7) (p : ℕ), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.LocBasis D p (TaylorLogMetric.YYl D L L') b → ∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (b i *ᵥ x) ∈ L' := by
  intro D p hA0 N N' L L' r b hb i
  obtain ⟨s, hs, hsb⟩ := hb.2.1 i
  obtain ⟨t, ht, h⟩ := yy_maps D hA0 hsb
  refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_⟩
  have := h x hx
  rwa [Matrix.smul_mulVec, smul_smul, ← Nat.cast_mul] at this

end GlobalTheory.TwV.YYMaps
