import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SwapMp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MeasurablePhiInv

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem pi_const_smul {ι : Type} [Fintype ι] (x : ℝ) :
    Measure.pi (fun _ : ι => ENNReal.ofReal x • (volume : Measure ℂ)) =
      ENNReal.ofReal x ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  have hsf : SigmaFinite (ENNReal.ofReal x • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (x.toNNReal • (volume : Measure ℂ)))
  refine Measure.pi_eq (fun t _ => ?_)
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

def embS {K : Type} [Field K] {ι : Type} (φ : ι → (K →+* ℂ)) (s : ℂ) : K →+ (ι → ℂ) where
  toFun a := fun i => s * φ i a
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]

theorem covol_oneT (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ)
    (B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ))
    (hBm : ∀ p, Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : P → ι → ℂ), B p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (hinv : ∀ γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : P → ι → ℂ,
      (∀ p, γ' p - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧ ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (Kset : Set (P → ι → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ g, ∃! γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧ mlaw B γ g ∈ Kset) :
    (Measure.pi fun _ : P => Measure.pi fun _ : ι => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c ^ Fintype.card ι • (volume : Measure (ι → ℂ))) := by
    rw [show ENNReal.ofReal c ^ Fintype.card ι = ((c.toNNReal ^ Fintype.card ι : NNReal) : ENNReal) by
      rw [ENNReal.coe_pow]; rfl]
    exact (inferInstance : SigmaFinite ((c.toNNReal ^ Fintype.card ι) • (volume : Measure (ι → ℂ))))
  have hFex : ∀ p, ∃ F : Set (ι → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : Λ p, (fun i => s p * φ i a) + v ∈ F := fun p =>
    exists_fd K ι φ σ hφ (I p) (Λ p) (hΛ p) (by rw [hk p]; exact hk0 p) (s p) (hs p)
  choose F hFm hFd using hFex
  have hFd' : ∀ p (v : ι → ℂ), ∃! a : (Λ p).map (embS φ (s p)), (a : ι → ℂ) + v ∈ F p := by
    intro p v
    obtain ⟨a, ha, hu⟩ := hFd p v
    refine ⟨⟨embS φ (s p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨b, hb⟩ hbF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.mp hb
    have hae := hu ⟨a', ha'⟩ hbF
    subst hae
    rfl
  have hcK : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hcA : ∀ p, Countable ((Λ p).map (embS φ (s p))) := fun p =>
    Function.Surjective.countable
      (f := fun a : Λ p => (⟨embS φ (s p) a, AddSubgroup.mem_map_of_mem _ a.2⟩ :
        (Λ p).map (embS φ (s p))))
      (by
        rintro ⟨b, hb⟩
        obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hb
        exact ⟨⟨a, ha⟩, rfl⟩)
  rw [pi_const_smul c]
  rw [triFundT P (fun _ => ι → ℂ) (fun _ => ENNReal.ofReal c ^ Fintype.card ι • volume) h B hBm hBd
    hB0 τ hτ (fun p => (Λ p).map (embS φ (s p))) hinv F hFm hFd' Kset hK hKd]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, idealCovolC K ι φ σ hφ (I p) (Λ p) (hΛ p) (k p) (hk p)
    (hk0 p) (s p) (hs p) (F p) (hFm p) (hFd p), ← ENNReal.ofReal_pow hc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Formalism.L2.SG.NGCut.SplitEmbedding
