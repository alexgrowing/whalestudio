import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAG

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

theorem disc_lattice (hd : d.AxH 𝒜) (h : d.S1) :
    d.De hd h ≠ 0 ∧ ∀ la, (d.htOf hd h).Ila la ≠ ⊤ ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
  have key : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (d.htOf hd h).Ila la ≠ ⊤ ∧ d.De hd h ≠ 0 ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
    intro la
    obtain ⟨n, t, N, hI, hN, u, hu, hDe⟩ := d.disc_at hd h la
    have hIL : d.IL h hd.sel hd.a4.choose la = (((d.htOf hd h).Ila la).toNat : ℝ) := rfl
    refine ⟨by rw [hI]; exact ENat.coe_ne_top n, ?_, ?_⟩
    · rw [hDe, algK_unif]
      exact mul_ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
        (unifOp_irreducible d.D d.N la).ne_zero))
        ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr hu.ne_zero)
    · rw [hIL, hI, d.gOrd_eq la hu hDe, hN, ENat.toNat_natCast]
      push_cast
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let la0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩
  exact ⟨(key la0).2.1, fun la => ⟨(key la).1, (key la).2.2⟩⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
