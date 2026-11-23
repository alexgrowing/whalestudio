import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.CutLatticeNormBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem dot_lt {K : Type} [NormedField K] [IsUltrametricDist K] {N : ℕ} (P P' Q Q' : Fin N → K)
    (hP : ∀ k, ‖P k‖ ≤ 1) (hP' : ∀ k, ‖P' k‖ ≤ 1) (h : ∀ k, ‖P k - Q k‖ < 1) (h' : ∀ k, ‖P' k - Q' k‖ < 1)
    (hQ : ‖∑ k, Q k * Q' k‖ < 1) : ‖P ⬝ᵥ P'‖ < 1 := by
  have hadd : ∀ x y : K, ‖x‖ < 1 → ‖y‖ < 1 → ‖x + y‖ < 1 := fun x y hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  have e : P ⬝ᵥ P' = ∑ k, ((P k - Q k) * P' k + Q k * (P' k - Q' k)) + ∑ k, Q k * Q' k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  refine hadd _ _ ?_ hQ
  refine Finset.sum_induction _ (fun x : K => ‖x‖ < 1) hadd (by simp) fun k _ => hadd _ _ ?_ ?_
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hP' k)).trans_lt (h k)
  · have hq : ‖Q k‖ ≤ 1 := by
      have : Q k = -(P k - Q k) + P k := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_neg]; exact (h k).le) (hP k))
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq).trans_lt (h' k)

private theorem pr_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] (c : K) (y : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (c • y) a = c * pr Dw y a := by
  simp [pr]

theorem UpperTheory.cut_lattice_two_embeddings_bound :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n g : ℕ) (h : Dw.La → Fin g → ℂ_[p]) (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) (Λ : Set (Fin g → ℂ_[p])), PtData Dw p n h b Λ → ∀ (σ σ' : 𝓞 E →+* ℂ_[p]) (M N r s : ℕ) (a : Fin M → Dw.La) (T S : Fin N → Fin M → ℂ_[p]) (δ δ' : ℂ_[p]) (A : Fin r → Fin g → ℂ_[p]) (A' : Fin s → Fin g → ℂ_[p]), CutL Dw σ a T δ → CutL Dw σ' a S δ' → DualL Dw σ' a T S → δ ≠ 0 → ‖δ‖ ≤ 1 → ‖δ'‖ = 1 → (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ‖ → LinearIndependent ℂ_[p] A → LinearIndependent ℂ_[p] A' → (∀ i, IsEigL Dw σ (b (A i))) → (∀ i, IsEigL Dw σ' (b (A' i))) → ∀ (u : Fin r → ℂ_[p]) (u' : Fin s → ℂ_[p]), (∀ k, ‖(covMat T (fun m => h (a m)) A *ᵥ u) k‖ ≤ 1) → (∀ k, ‖(covMat S (fun m => h (a m)) A' *ᵥ u') k‖ ≤ 1) → ‖(covMat T (fun m => h (a m)) A *ᵥ u) ⬝ᵥ (covMat S (fun m => h (a m)) A' *ᵥ u')‖ < 1 := by
  intro E _ _ _ H Dw p _ n g h b Λ hD σ σ' M N r s a T S δ δ' A A' hT hS hdual hδ0 hδ1 hδ' hn hA hA' hE hE' u u' hu hu'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hδp : 0 < ‖δ‖ := norm_pos_iff.2 hδ0
  have hδ'0 : δ' ≠ 0 := by
    rw [← norm_pos_iff, hδ']; exact one_pos
  have hn' : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ'‖ := by
    rw [hδ']
    exact hn.trans (by gcongr)
  obtain ⟨-, h1, h2⟩ := (UpperTheory.cut_lattice_norm_bound E H Dw p n g h b Λ hD σ M N r a T δ A hT hδ0 hδ1 hn hA hE).2.2 u hu
  obtain ⟨-, h1', h2'⟩ :=
    (UpperTheory.cut_lattice_norm_bound E H Dw p n g h b Λ hD σ' M N s a S δ' A' hS hδ'0 hδ'.le hn' hA' hE').2.2 u' hu'
  have hEv : IsEigL Dw σ' (b (∑ i, u' i • A' i)) := by
    intro o
    simp only [map_sum, map_smul, hE' _ o, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine dot_lt _ _ _ _ hu hu' h2 h2' ?_
  rw [hdual _ _ hEv, norm_neg]
  have hI := hD.2.2.2 (δ • ∑ i, u i • A i) (δ' • ∑ i, u' i • A' i)
    (fun o => by rw [map_smul, pr_smul']; exact h1 o) (fun o => by rw [map_smul, pr_smul']; exact h1' o)
  generalize ∑ i, u i • A i = v at hI ⊢
  generalize ∑ i, u' i • A' i = v' at hI ⊢
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul, hδ', _root_.one_mul] at hI
  rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)] at hI
  refine (?_ : ∀ x : ℝ, 0 ≤ x → ‖δ‖ * x * (p : ℝ) ^ n ≤ 1 → x < 1) _ (norm_nonneg _) hI
  intro x hx hI
  have h3 : (p : ℝ) ^ 2 * x ≤ 1 := by
    calc (p : ℝ) ^ 2 * x ≤ (p : ℝ) ^ n * ‖δ‖ * x := by gcongr
      _ = ‖δ‖ * x * (p : ℝ) ^ n := by ring
      _ ≤ 1 := hI
  have h4 : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  by_contra hc
  have hc' := not_lt.1 hc
  nlinarith
