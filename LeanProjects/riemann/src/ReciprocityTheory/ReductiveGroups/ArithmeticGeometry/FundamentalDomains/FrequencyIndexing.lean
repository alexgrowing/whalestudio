import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeFourierExpansion

namespace ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))

noncomputable def νk (k : Fin n → ℤ) : ι → ℝ :=
  fun τ => (∑ j, (k j : ℝ) * ω.repr (Pi.single τ 1) j) / 2

lemma pairing (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) (v : ι → ℝ) :
    ∑ τ, ν τ * v τ = (∑ j, (k j : ℝ) * ω.repr v j) / 2 := by
  have hv : v = ∑ j, ω.repr v j • ω j := (ω.sum_repr v).symm
  have h1 : ∀ j, (k j : ℝ) * ω.repr v j / 2 = ∑ τ, ν τ * (ω.repr v j * ω j τ) := by
    intro j
    rw [← hk j, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl (fun τ _ => by ring)
  rw [Finset.sum_div]
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_lhs => rw [hv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma repr_sum_single (v : ι → ℝ) (j : Fin n) :
    ∑ τ, v τ * ω.repr (Pi.single τ 1) j = ω.repr v j := by
  have hv : v = ∑ τ, v τ • (Pi.single τ (1 : ℝ) : ι → ℝ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

lemma νk_spec (k : Fin n → ℤ) (i : Fin n) : 2 * ∑ τ, νk ω k τ * ω i τ = k i := by
  have h : ∀ τ, νk ω k τ * ω i τ =
      (∑ j, (k j : ℝ) * (ω i τ * ω.repr (Pi.single τ 1) j)) / 2 := by
    intro τ
    simp only [νk]
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, repr_sum_single, Module.Basis.repr_self, Finsupp.single_apply]
  simp
  ring

lemma νk_injective : Function.Injective (νk ω) := by
  intro k k' h
  funext i
  have h1 := νk_spec ω k i
  have h2 := νk_spec ω k' i
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

lemma eq_νk (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) : ν = νk ω k := by
  funext τ
  have h1 := pairing ω ν k hk (Pi.single τ 1)
  have h2 := pairing ω (νk ω k) k (νk_spec ω k) (Pi.single τ 1)
  have e : ∀ μ : ι → ℝ, ∑ σ, μ σ * (Pi.single τ (1 : ℝ) : ι → ℝ) σ = μ τ := by
    intro μ
    simp [Pi.single_apply]
  rw [e] at h1 h2
  rw [h1, h2]

end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
