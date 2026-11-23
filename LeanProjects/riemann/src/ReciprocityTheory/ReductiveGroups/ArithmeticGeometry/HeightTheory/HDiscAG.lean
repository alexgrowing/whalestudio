import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAF

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

theorem prod_zpow_eq {ι G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_at (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ n t : ℕ, ∃ N : ℤ, (d.htOf hd h).Ila la = n ∧ d.NlaG h d.wF hd.a4.choose la = N ∧
      ∃ u : Op d.D d.N la, IsUnit u ∧ d.De hd h =
        (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ (((2 * n + t : ℕ) : ℤ) - 2 * N) *
          OpToKT d.D d.N la u := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  haveI := Op_isDVR (K := K) d.D d.N la
  haveI := isFractionRing_Op (K := K) d.D d.N la
  have hF := fun c => d.comp_facts hd h la c
  haveI : ∀ c, IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    fun c => (hF c).2.1
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.1
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.2.1
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    d.ord c (d.Wres c w) d.wF (hd.a4.choose c)
  choose g hg0 hgw hgiff using fun c => d.comp_g hd h la c (n c)
  have hset : d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la =
      {y | ∀ c, g c * y c ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)} := by
    ext y
    simp only [AdmissibleOmegaFamiliesAtPrimeOfSection, Set.mem_setOf_eq]
    exact forall_congr' fun c => hgiff c (y c)
  have hb : ∀ k c, g c * d.bvecG hd.sel hd.a4.choose k c ∈
      integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun k c =>
    (hgiff c _).mp (fun w hw => d.b_mem hd h la k c w hw)
  obtain ⟨nn, t, u, hlen, hdisc⟩ := HDiscLat.lattice_main (R := Op d.D d.N la)
    (F := KTf K d.D d.N) (unifOp_irreducible d.D d.N la) g hg0 (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) hb (d.b_linIndep hd h)
  choose uN huN hN using fun c => d.comp_norm hd h la c (hg0 c) (n c) (hgw c)
  let Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (_ : w ∈ d.PlOver la c), (d.fze h c w : ℤ) * n c w
  have hfin : ∀ c, (d.PlOver la c).Finite := fun c => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hF c
    rw [d.plOver_eq h la c]
    exact ValPl.placesOver_finite (F := KTf K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N)
  refine ⟨nn, t, ∑ c, Nc c, ?_, ?_, ?_⟩
  · change Module.length (Op d.D d.N la)
      (↥(Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)) ⧸
        (Submodule.span (Op d.D d.N la) (Set.range (d.bvecG hd.sel hd.a4.choose))).comap
          (Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)).subtype) = nn
    rw [hset]
    exact hlen
  · simp only [NlaG, Nc]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin c), finsum_mem_eq_finite_toFinset_sum _ (hfin c)]
    push_cast
    rfl
  · set X := OpToKT d.D d.N la (unifOp d.D d.N la) with hX
    have hX0 : X ≠ 0 := (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
      (unifOp_irreducible d.D d.N la).ne_zero
    let U : (Op d.D d.N la)ˣ := ∏ c, (huN c).unit
    have hprod : ∏ c, Algebra.norm (KTf K d.D d.N) (g c) =
        X ^ (∑ c, Nc c) * OpToKT d.D d.N la (U : Op d.D d.N la) := by
      rw [Finset.prod_congr rfl fun c _ => hN c, Finset.prod_mul_distrib, prod_zpow_eq hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    refine ⟨↑(u * U⁻¹ * U⁻¹), Units.isUnit _, ?_⟩
    rw [algK_unif, ← hX]
    set V := OpToKT d.D d.N la (U : Op d.D d.N la)
    set V' := OpToKT d.D d.N la ((U⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    set Y := X ^ (∑ c, Nc c)
    have hY : Y ≠ 0 := zpow_ne_zero _ hX0
    have h2 : X ^ (2 * ∑ c, Nc c) = Y ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hone : (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = 1 := by
      calc (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = (Y ^ 2 * (Y ^ 2)⁻¹) * ((V * V') * (V * V')) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hY), hU]; ring
    have hdisc' : d.De hd h * (Y * V) ^ 2 =
        OpToKT d.D d.N la ↑u * X ^ (2 * nn + t) := by
      rw [← map_pow, ← map_mul]
      exact hdisc
    rw [zpow_sub₀ hX0, zpow_natCast, h2, Units.val_mul, Units.val_mul, map_mul, map_mul]
    calc d.De hd h = d.De hd h * ((Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V')) := by rw [hone, mul_one]
      _ = (d.De hd h * (Y * V) ^ 2) * ((Y ^ 2)⁻¹ * V' * V') := by ring
      _ = _ := by rw [hdisc', div_eq_mul_inv]; ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
