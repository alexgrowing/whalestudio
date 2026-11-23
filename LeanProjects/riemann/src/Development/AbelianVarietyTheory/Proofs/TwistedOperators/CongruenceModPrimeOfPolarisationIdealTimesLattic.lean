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

namespace GlobalTheory.LevkLoc

theorem smul_mem_of_isAA {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (h : IsAA Λ ΛT) (c : D.host.E)
    (hc : ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c * x) : ∀ x ∈ Λ, c • x ∈ ΛT := by
  intro x hx
  have hx' := (h x).1 hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hc a ha
    rw [smul_smul, ← hb]
    have : ((b : D.host.E)) • t = b • t := (algebraMap_smul D.host.E b t)
    rw [this]
    exact ΛT.smul_mem b ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact ΛT.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact ΛT.neg_mem hx

theorem smul_mem_ideal_smul {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (P : Ideal (𝓞 D.host.E)) (c : D.host.E)
    (h : ∀ x ∈ Λ, c • x ∈ ΛT) : ∀ x ∈ P • Λ, c • x ∈ P • ΛT := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun p hp y hy => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul hp (h y hy)
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

theorem congr_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT →
    ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) →
    ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  intro D k Λ ΛT P hP hAA m hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity D
  choose b hb using fun i => hc i (a i) (ha i)
  have hb1 : ∑ i, b i = 1 := by
    have : ((∑ i, b i : 𝓞 D.host.E) : D.host.E) = ((1 : 𝓞 D.host.E) : D.host.E) := by
      push_cast
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact hb i
    exact RingOfIntegers.ext this
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hb1]
    exact Ideal.sum_mem _ fun i _ => hcon i
  refine ⟨b i, hi, fun u hu => ?_⟩
  have hA : ∀ t ∈ ΛT, a i • t ∈ Λ := fun t ht =>
    (hAA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, t, ht, rfl⟩)
  have hC : ∀ x ∈ P • Λ, c i • x ∈ P • ΛT :=
    smul_mem_ideal_smul P (c i) (smul_mem_of_isAA hAA (c i) (hc i))
  have hu' := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D ΛT Λ (a i) hA u hu
  have h1 := hm _ hu'
  have h2 := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D (P • Λ) (P • ΛT) (c i) hC _ h1
  convert h2 using 1
  rw [Matrix.mulVec_smul, ← smul_sub, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hb i]

end GlobalTheory.LevkLoc
