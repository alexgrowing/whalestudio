import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymResidue

theorem dsum_shift {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      ∑ i ∈ Finset.range (n - 1), f i (i + 1) := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      if (i : ℕ) + 1 < n then f i ((i : ℕ) + 1) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = (i : ℕ) + 1 then f i j else 0) n]
    simp [Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < n then f i (i + 1) else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem intAt_sum {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (f : ℕ → E)
    (h : ∀ i < n, IntAt P (f i)) : IntAt P (∑ i ∈ Finset.range n, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun a b ha hb => IntAt.add ha hb) ?_ ?_
  · simpa using IntAt.coe P 0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)

end GlobalTheory.SymResidue

open GlobalTheory.SymResidue in
theorem GlobalTheory.symLevel_lam_residue : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  have hent : ∀ a b, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val a b =
      ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b)) := by
    intro a b; rw [hg]; rfl
  set A : E := ∑ i ∈ Finset.range (κ - 1), M i (i + 1) with hA
  set B : E := ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1) with hB
  have hAi : IntAt P A := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hBi : IntAt P B := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hsimple : GlobalTheory.RootEx.simpleSum (g : GL (Fin κ ⊕ Fin (s + 1)) k) = ι B := by
    unfold GlobalTheory.RootEx.simpleSum
    simp only [hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inr]
    rw [dsum_shift (s + 1) (fun i j => ι (M (κ + i) (κ + j))), hB, map_sum]
    have : κ + s + 1 - κ - 1 = s + 1 - 1 := by omega
    rw [this]
    rfl
  have hsuper : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (g : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = ι A := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl]
    rw [dsum_shift κ (fun i j => ι (M i j)), hA, map_sum]
  have hdiv : ∀ X : E, ((S.ϖ⁻¹ : kˣ) : k) * ι X = ι (X / (q : E)) := by
    intro X
    rw [Units.val_inv_eq_inv_val, hT.compl.unif, ← map_inv₀, ← map_mul, div_eq_inv_mul]
  rw [S.sym.2 g, hsimple, hsuper, hdiv, hdiv, hT.psi B hBi, hT.psi A hAi, ← map_mul,
    ← AddChar.map_add_eq_mul, ← reduction_add hBi hAi, add_comm B A]
