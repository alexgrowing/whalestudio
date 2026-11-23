import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OmPoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscProduct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscHadamard
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_global (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
      (Module.finrank ℚ K : ℝ) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨haG0, ⟨a, b, hab⟩, Om, hOm, hOm0, hOmH⟩ := d.om_poly hd h
  obtain ⟨hs1, hs2, heq⟩ := d.disc_product hd h hI2be a b hab Om hOm
  refine ⟨hs1, hs2, ?_⟩
  rw [heq]
  have ha4 : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := by
    first
    | exact hd.a4.choose_spec
    | exact hd.a4.choose_spec.1
    | exact fun c => hd.a4.choose_spec.1 c
    | exact fun c => ⟨hd.a4.choose_spec.1 c, hd.a4.choose_spec.2 c⟩
  have hH : d.Hgt h d.wF hd.a4.choose = d.Hgt h d.wF ta' :=
    (d.h_ind hd h hI2be).1 d.wF hd.a4.choose ta' (by simp) ha4 hta'
  have haG : d.aG h d.wF hd.a4.choose = d.aG h d.wF ta' :=
    (d.arithDegree_additive hd h).1 d.wF hd.a4.choose ta' ha4 hta'
  have hcard : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    have hc : 0 < Fintype.card (K →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
      | exact Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hc
  have hmean : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) := by
    unfold meanK
    rw [div_le_iff₀ hcard]
    calc ∑ sg, (d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg)
        ≤ ∑ sg, (d.del * Real.log d.del +
            2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) :=
          Finset.sum_le_sum fun sg _ => d.disc_hadamard hd h hI2be a b hab sg
      _ = (d.del * Real.log d.del + 2 * ((∑ k, ∑ sg,
            Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) / (Fintype.card (K →+* ℂ) : ℝ))) *
            (Fintype.card (K →+* ℂ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum, Finset.sum_comm, add_mul, mul_assoc (2 : ℝ),
            div_mul_cancel₀ _ hcard.ne']
          ring
      _ = _ := by rw [Finset.sum_div]
  have hh0 : -(ReciprocityTheory.MultiplicativeHeights.h0 Om) ≤
      2 * d.D * d.aG h d.wF hd.a4.choose * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ Om (Nat.succ_pos _) hOm0 hOmH
    have ht : ((d.aG h d.wF hd.a4.choose).toNat : ℝ) = (d.aG h d.wF hd.a4.choose : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg haG0
    simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, eq_self_iff_true, if_true, if_false,
      ite_true, ite_false, Nat.cast_zero, zero_mul, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h1
    rw [ht] at h1
    linear_combination h1
  rw [hH, ← haG]
  linarith [hmean, hh0]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
