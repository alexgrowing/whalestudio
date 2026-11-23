import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
open scoped ContDiff

namespace GlobalTheory.Mem.JetChain

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem eq_sum_coordX (z : VCx ι a b) : z = ∑ k : DVar ι a b, z k.1 k.2.1 k.2.2 • coordX k := by
  classical
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp [coordX]
  · rintro ⟨τ', i', j'⟩ _ h
    have : ¬ (τ = τ' ∧ i = i' ∧ j = j') := by
      rintro ⟨rfl, rfl, rfl⟩
      exact h rfl
    simp [coordX, this]
  · simp

theorem exists_derivAt0 (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ} (f : Fin n → DVar ι a b) :
    ∃ e : DVar ι a b →₀ ℕ, e.degree = n ∧ iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  set e : DVar ι a b →₀ ℕ := Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)) with he
  have hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b)) := by
    rw [he, Multiset.toFinsupp_toMultiset]
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  refine ⟨e, ?_, ?_⟩
  · rw [← hc, Finsupp.card_toMultiset]; rfl
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem derivAt0_comp_mem : ∀ (ι : Type) [Fintype ι] (a b n : ℕ) (K₀ : Subfield ℂ) (G : VCx ι a b → ℂ) (L : VCx ι a b →ₗ[ℂ] VCx ι a b) (κ : ℂ), (∀ k : ℕ, ContDiff ℂ k G) → (∀ k τ i j, L (coordX k) τ i j ∈ K₀) → (∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 G e ∈ K₀) → ∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 (fun z => G (L z)) e ∈ K₀ := by
  intro ι _ a b n K₀ G L κ hG hL hK e he
  classical
  have hc : (Finsupp.toMultiset e).card = n := by
    rw [← he, Finsupp.card_toMultiset]; rfl
  subst hc
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap L
  have h1 : (fun z => G (L z)) = G ∘ T := rfl
  have key : ∀ g : Fin (Finsupp.toMultiset e).card → DVar ι a b,
      κ * iteratedFDeriv ℂ _ G 0 (fun i => L (coordX (g i))) ∈ K₀ := by
    intro g
    have h2 : (fun i => L (coordX (g i))) =
        fun i => ∑ k : DVar ι a b, L (coordX (g i)) k.1 k.2.1 k.2.2 • coordX k :=
      funext fun i => eq_sum_coordX _
    rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
    refine sum_mem fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_left_comm]
    refine mul_mem (prod_mem fun i _ => hL _ _ _ _) ?_
    obtain ⟨e', he', h⟩ := exists_derivAt0 G hG f
    rw [h]
    exact hK e' he'
  unfold derivAt0
  rw [h1, T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact key _

end GlobalTheory.Mem.JetChain
