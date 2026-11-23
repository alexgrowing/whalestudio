import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealProdS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TermId
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TsupportUnit2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_exch {α ι : Type} [Fintype ι] (T s : Set α) (hs : s.Finite) (F : α → ℂ) (c : ι → ℂ)
    (G : ι → α → ℂ) (h : ∀ p ∈ T, F p = ∑ i, c i * G i p) (h0 : ∀ i, ∀ p ∈ T, G i p ≠ 0 → p ∈ s) :
    ∑ᶠ p ∈ T, F p = ∑ i, c i * ∑ᶠ p ∈ T, G i p := by
  have hf : (T ∩ s).Finite := hs.inter_of_right T
  have e1 : ∀ i, ∑ᶠ p ∈ T, G i p = ∑ p ∈ hf.toFinset, G i p := fun i => by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    exact finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, h0 i p hT hp⟩, fun hT => hT.1⟩
  have e2 : ∑ᶠ p ∈ T, F p = ∑ p ∈ hf.toFinset, F p := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    refine finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, ?_⟩, fun hT => hT.1⟩
    by_contra hn
    apply hp
    rw [h p hT]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [not_not.1 fun hG => hn (h0 i p hT hG), mul_zero]
  simp only [e1, e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => h p (hf.mem_toFinset.1 hp).1

private theorem ne_zero_of_finprod {α : Type} (S : Set α) (g : α → ℂ) (hf : (S ∩ Function.mulSupport g).Finite)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w hw h0
  apply h
  rw [finprod_mem_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := w) ?_ h0
  simp [hw, Function.mem_mulSupport, h0]

theorem UpperTheory.ConvolutionTheory.G2.g2s :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.G2s := by
  intro E _ _ _ hE n _ μ e hμ lam
  have hle : ∀ a : Fin (n + 1), (a : ℕ) ≤ n := fun a => Nat.lt_succ_iff.1 a.2
  choose ι fι l₁ l₂ sg hu hw hch using fun a : Fin (n + 1) =>
    UpperTheory.ConvolutionTheory.G2.realProdS E n a (n - a) (Nat.add_sub_cancel' (hle a)) e hμ.2.2.2.1 lam
  have key : ∀ a : Fin (n + 1), ((a : ℕ) = 0 ∨ n - a = 0) →
      ∃ i : Σ a, ι a, (i.1 : ℕ) = a ∧ sg i.1 i.2 = 1 ∧ ∀ j : Σ a, ι a, (j.1 : ℕ) = a → j = i := fun a h => by
    obtain ⟨⟨i₀, hi⟩, hs⟩ := hu a h
    refine ⟨⟨a, i₀⟩, rfl, hs i₀, ?_⟩
    rintro ⟨a', j⟩ hj
    obtain rfl : a' = a := Fin.ext hj
    rw [hi j]
  refine ⟨Σ a, ι a, inferInstance, fun i => i.1, fun i => l₁ i.1 i.2, fun i => l₂ i.1 i.2, fun i => sg i.1 i.2,
    fun i => ⟨hle i.1, hw i.1 i.2⟩, key (Fin.last n) (Or.inr (by simp)), key 0 (Or.inl rfl), ?_⟩
  intro S hS K' f φ _ _ hφ
  unfold geomU
  rw [Finset.sum_range, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨⟨K₁, K₂, -, -, hH, hU⟩, hM⟩ := hφ a (hle a)
  have hU' : ∀ᶠ w in cofinite, φ a w = UpperTheory.ConvolutionTheory.G2.unit2 a (n - a) w := hU
  have hT := UpperTheory.ConvolutionTheory.G2.termId E hE μ e hμ S hS n a (n - a) f (φ a) hU' hM
  refine finsum_exch _ _ (UpperTheory.ConvolutionTheory.G2.finP E hE a (n - a) S hS (φ a) (fun w => (hH w).1) hU') _ _ _ ?_ ?_
  · rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩
    have k := hch a P₁ P₂ h₁ h₂ hc
    rw [(hT P₁ P₂ h₁ h₂ hc).2, (GlobalTheory.BCT.KapMul.kap_mul E hE a (n - a) P₁ P₂ h₁ h₂ hc).1]
    calc _ = kap P₁ * kap P₂ * (∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w P₁) (atPl w P₂) (φ a w)) *
          ((∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂)) := by ring
      _ = _ := by
        rw [k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  · rintro i ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩ hG
    exact ⟨h₁, h₂, ne_zero_of_finprod S _ (hT P₁ P₂ h₁ h₂ hc).1 (right_ne_zero_of_mul hG)⟩
