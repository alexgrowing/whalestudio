import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemHermitianLatticeAdelicCompletionOfSmulLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevMoveAA

theorem isMov_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  intro D k Λ ΛT m hA hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity D
  have h1 : ∀ i, ∀ x ∈ ΛT, a i • x ∈ Λ := fun i x hx =>
    (hA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, x, hx, rfl⟩)
  have h2 : ∀ i, ∀ x ∈ Λ, c i • x ∈ ΛT := by
    intro i x hx
    have hx' := (hA x).1 hx
    clear hx
    induction hx' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨a', ha', t, ht, rfl⟩ := hu
      obtain ⟨b, hb⟩ := hc i a' ha'
      rw [smul_smul, ← hb]
      exact ΛT.smul_of_tower_mem b ht
    | zero => simp
    | add x y _ _ ihx ihy => rw [smul_add]; exact ΛT.add_mem ihx ihy
    | neg x _ ihx => rw [smul_neg]; exact ΛT.neg_mem ihx
  have hs1 : ∀ i, ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u ∈ hatV Λ :=
    fun i => GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D ΛT Λ (a i) (h1 i)
  have hs2 : ∀ i, ∀ u ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • u ∈ hatV ΛT :=
    fun i => GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D Λ ΛT (c i) (h2 i)
  have key : ∀ u : Fin k → AfE D,
      ∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = u := by
    intro u
    simp_rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Finset.sum_smul,
      ← TensorProduct.tmul_sum]
    rw [show ∑ i, c i * a i = 1 by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [← Algebra.TensorProduct.one_def, one_smul]
  intro u
  constructor
  · intro hu
    have hw : ∀ i, ∃ w ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = m *ᵥ w :=
      fun i => (hm _).1 (hs1 i u hu)
    choose w hwΛ hwe using hw
    refine ⟨∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • w i,
      AddSubgroup.sum_mem _ fun i _ => hs2 i _ (hwΛ i), ?_⟩
    rw [Matrix.mulVec_sum]
    conv_lhs => rw [← key u]
    exact Finset.sum_congr rfl fun i _ => by rw [hwe i, Matrix.mulVec_smul]
  · rintro ⟨u₀, hu₀, rfl⟩
    rw [← key u₀, Matrix.mulVec_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact hs2 i _ ((hm _).2 ⟨_, hs1 i u₀ hu₀, rfl⟩)

end GlobalTheory.LevMoveAA

end
