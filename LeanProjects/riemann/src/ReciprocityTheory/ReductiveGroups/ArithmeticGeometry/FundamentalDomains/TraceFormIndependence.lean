import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def efr (X : Data E r) (v w : X.Ψ → Fin r → ℂ) : ℝ :=
  ∑ τ, 2 * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ)).re

lemma add_conj' (w : ℂ) : w + conj w = 2 * (w.re : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma trace_re (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have hall : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
    have h' : (algebraMap ℚ ℂ) (Algebra.trace ℚ E z) = ((Algebra.trace ℚ E z : ℚ) : ℂ) :=
      eq_ratCast _ _
    rw [← h', h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  have hconj : ∑ σ ∈ X.Ψᶜ, σ z = ∑ σ ∈ X.Ψ, conj (σ z) := by
    apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ)
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      rw [X.cmType, hcc]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact hcc σ
    · intro σ _
      exact hcc σ
    · intro σ _
      simp [ComplexEmbedding.conjugate_coe_eq]
  push_cast
  rw [hall, ← Finset.sum_add_sum_compl X.Ψ, hconj, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  exact Finset.sum_congr rfl fun τ _ => add_conj' _

lemma EF_eq_efr (X : Data E r) (x y : Fin r → E) :
    ((EFf X.ξ0 X.Gm x y : ℚ) : ℝ) = efr X (X.embV x) (X.embV y) := by
  unfold EFf efr
  rw [trace_re X]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul]
  congr 3
  simp only [herm, hermC, map_sum, map_mul, ReciprocityTheory.ChartRestriction.G.FD.emb_cc, Data.embV, Data.emb]

lemma hC_sub_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma efr_add_right (X : Data E r) (v w w' : X.Ψ → Fin r → ℂ) :
    efr X v (w + w') = efr X v w + efr X v w' := by
  unfold efr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

lemma efr_sub_right (X : Data E r) (v w w' : X.Ψ → Fin r → ℂ) :
    efr X v (w - w') = efr X v w - efr X v w' := by
  unfold efr
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

lemma efr_add_left (X : Data E r) (v v' w : X.Ψ → Fin r → ℂ) :
    efr X (v + v') w = efr X v w + efr X v' w := by
  unfold efr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, Complex.add_re]

lemma efr_sub_left (X : Data E r) (v v' w : X.Ψ → Fin r → ℂ) :
    efr X (v - v') w = efr X v w - efr X v' w := by
  unfold efr
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub, Complex.sub_re]

lemma efr_nsmul_right (X : Data E r) (n : ℕ) (v w : X.Ψ → Fin r → ℂ) :
    efr X v ((n : ℂ) • w) = n * efr X v w := by
  unfold efr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : hermC τ.1 X.Gm (v τ) (((n : ℂ) • w) τ) = (n : ℂ) * hermC τ.1 X.Gm (v τ) (w τ) := by
    simp only [hermC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    ring
  rw [h, mul_left_comm]
  have e : ((n : ℂ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ))).re =
      (n : ℝ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ)).re := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [e]
  ring

lemma efr_nsmul_left (X : Data E r) (n : ℕ) (v w : X.Ψ → Fin r → ℂ) :
    efr X ((n : ℂ) • v) w = n * efr X v w := by
  unfold efr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : hermC τ.1 X.Gm (((n : ℂ) • v) τ) (w τ) = (n : ℂ) * hermC τ.1 X.Gm (v τ) (w τ) := by
    simp only [hermC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, mul_left_comm]
  have e : ((n : ℂ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ))).re =
      (n : ℝ) * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ)).re := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [e]
  ring

lemma eq_zero_of_indep (X : Data E r) (d : X.Ψ → ℂ)
    (h : ∀ β : 𝓞 E, ∑ τ : X.Ψ, 2 * (d τ * conj (τ.1 (β : E))).re = 0) (τ0 : X.Ψ) :
    d τ0 = 0 := by
  classical
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  let d' : (E →+* ℂ) → ℂ := fun σ => if hσ : σ ∈ X.Ψ then d ⟨σ, hσ⟩ else 0
  have hd' : ∀ τ : X.Ψ, d' τ.1 = d τ := fun τ => by simp [d', τ.2]
  let c : (E →+* ℂ) → ℂ := fun σ =>
    if σ ∈ X.Ψ then conj (d' σ) else d' (ComplexEmbedding.conjugate σ)
  have hint : ∀ β : 𝓞 E, ∑ σ : E →+* ℂ, c σ * σ (β : E) = 0 := by
    intro β
    have hb' : ∑ τ ∈ X.Ψ, (d' τ * conj (τ (β : E)) + conj (d' τ * conj (τ (β : E)))) = 0 := by
      have h2 : ((∑ τ : X.Ψ, 2 * (d τ * conj (τ.1 (β : E))).re : ℝ) : ℂ) = 0 := by
        rw [h β]; simp
      push_cast at h2
      rw [← h2, ← Finset.sum_coe_sort X.Ψ]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hd', add_conj']
    rw [← Finset.sum_add_sum_compl X.Ψ]
    have h1 : ∑ σ ∈ X.Ψ, c σ * σ (β : E) = ∑ σ ∈ X.Ψ, conj (d' σ * conj (σ (β : E))) := by
      refine Finset.sum_congr rfl fun σ hσ => ?_
      simp [c, hσ]
    have h2 : ∑ σ ∈ X.Ψᶜ, c σ * σ (β : E) = ∑ σ ∈ X.Ψ, d' σ * conj (σ (β : E)) := by
      apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
        (fun σ => ComplexEmbedding.conjugate σ)
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
        rw [X.cmType, hcc]
        exact hσ
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
        exact (X.cmType σ).mp hσ
      · intro σ _
        exact hcc σ
      · intro σ _
        exact hcc σ
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ
        simp [c, hσ, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, h2, ← Finset.sum_add_distrib, ← hb']
    exact Finset.sum_congr rfl fun σ _ => add_comm _ _
  have hall : ∀ x : E, ∑ σ : E →+* ℂ, c σ * σ x = 0 := by
    intro x
    obtain ⟨y, hy, hyx⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
    have hx := hint ⟨y • x, hyx⟩
    change ∑ σ : E →+* ℂ, c σ * σ (y • x) = 0 at hx
    have e2 : ∑ σ : E →+* ℂ, c σ * σ (y • x) = (y : ℂ) * ∑ σ : E →+* ℂ, c σ * σ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [zsmul_eq_mul, map_mul, map_intCast]
      ring
    rw [e2] at hx
    exact (mul_eq_zero.mp hx).resolve_left (by exact_mod_cast hy)
  have hli := (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
    (fun a b hab => RingHom.ext fun x => by
      have := congrArg (fun f : E →* ℂ => f x) hab
      simpa using this)
  have hc0 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    simpa [Finset.sum_apply] using hall x)
  have hnot : ComplexEmbedding.conjugate τ0.1 ∉ X.Ψ := (X.cmType τ0.1).mp τ0.2
  have h0 := hc0 (ComplexEmbedding.conjugate τ0.1)
  simp only [c, hnot, if_false, hcc] at h0
  rw [← hd']
  exact h0

end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
