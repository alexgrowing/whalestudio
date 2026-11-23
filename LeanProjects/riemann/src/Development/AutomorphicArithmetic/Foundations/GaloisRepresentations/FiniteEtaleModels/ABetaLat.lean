import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem gen_facts {A : Type} [CommRing A] {a : A} {n : ℕ} {𝔟 : Ideal A} (G : IsGen a n 𝔟) :
    (n : A) ∈ 𝔟 ∧ ∀ c ∈ 𝔟, ∃ d, c * a = (n : A) * d := by
  have G' : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 = Ideal.span {(n : A)} := G
  have hle : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 ≤ 𝔟 :=
    Ideal.mul_le.mpr fun x _ y hy => 𝔟.mul_mem_left x hy
  have hN : (n : A) ∈ 𝔟 := by
    apply hle
    rw [G']
    exact Ideal.mem_span_singleton_self _
  refine ⟨hN, fun c hc => ?_⟩
  have hmem : a * c ∈ (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 :=
    Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
  rw [G', Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [mul_comm]; exact hd⟩

private theorem reindex_lattice_of_ideals {A O L : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup L] [Module O L]
    (cancel : ∀ k : ℕ, 0 < k → ∀ x y : L, k • x = k • y → x = y)
    (𝔟₁ 𝔟₂ : Ideal A) (W₁ W₂ : Submodule O L) (n m₁ : ℕ) (a₁ a₂ : A) (hn : 0 < n) (hm : 0 < m₁) (hle : 𝔟₁ ≤ 𝔟₂)
    (hn2 : (n : A) ∈ 𝔟₂) (hc2 : ∀ c ∈ 𝔟₂, ∃ d, c * a₂ = n * d)
    (BaseTypeSubspacesMapOntoBothSides : ∀ y : L, (∃ z, algebraMap A O a₁ • y = (n * m₁) • z) ↔ y ∈ W₁)
    (PairingFactorsThroughPeriods : ∀ x : L, (∀ c ∈ 𝔟₁, ∃ z, algebraMap A O c • x = (n * m₁) • z) →
      ∃ y z, x = algebraMap A O a₁ • y + (n * m₁) • z)
    (ProjectionSandwichLength : ∀ y : L, (∃ z, algebraMap A O a₂ • y = n • z) ↔ y ∈ W₂)
    (DegreeKernelLowerBound : ∀ x : L, (∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • x = n • z) → ∃ y z, x = algebraMap A O a₂ • y + n • z)
    (g : L →+ L) (h1 : ∀ (a : O) x, ∃ z, g (a • x) = a • g x + n • z)
    (h2 : ∀ x z, g x = n • z → ∃ v, x = n • v) (h3 : ∀ x, ∃ y z, g y = x + n • z) :
    ∃ β : L → L, (∀ x y, β (x + y) - (β x + β y) ∈ W₁) ∧ (∀ (c : O) x, β (c • x) - c • β x ∈ W₁) ∧
      (∀ y, β y ∈ W₁ ↔ y ∈ W₂) ∧
      (∀ x, (∀ c ∈ 𝔟₂, algebraMap A O c • x ∈ W₁) → ∃ y, x - β y ∈ W₁) ∧
      ∀ y, ∃ z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • β y + (n * m₁) • z := by
  have hnm : ∀ v : L, m₁ • (n • v) = (n * m₁) • v := by
    intro v
    rw [mul_comm, mul_smul]
  have memW1 : ∀ v : L, (∃ z, algebraMap A O a₁ • v = (n * m₁) • z) → v ∈ W₁ := fun v h => (BaseTypeSubspacesMapOntoBothSides v).mp h
  have ex : ∀ y : L, ∃ y' z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • y' + (n * m₁) • z := by
    intro y
    apply PairingFactorsThroughPeriods
    intro c hc
    obtain ⟨d, hd⟩ := hc2 c (hle hc)
    obtain ⟨z, hz⟩ := h1 (algebraMap A O c) (algebraMap A O a₂ • y)
    have e1 : algebraMap A O c • algebraMap A O a₂ • y = n • (algebraMap A O d • y) := by
      rw [smul_smul, ← map_mul, hd, map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]
    refine ⟨g (algebraMap A O d • y) - z, ?_⟩
    rw [e1, map_nsmul] at hz
    rw [smul_comm (algebraMap A O c) m₁, eq_sub_of_add_eq hz.symm, mul_comm n m₁, mul_smul]
    simp only [smul_sub]
  choose β z0 hβ using ex
  refine ⟨β, ?_, ?_, ?_, ?_, fun y => ⟨z0 y, hβ y⟩⟩
  · intro x y
    apply memW1
    refine ⟨z0 x + z0 y - z0 (x + y), ?_⟩
    have h := hβ (x + y)
    rw [smul_add, map_add, smul_add, hβ x, hβ y] at h
    rw [smul_sub, smul_add, eq_sub_of_add_eq h.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro c x
    apply memW1
    obtain ⟨w, hw⟩ := h1 c (algebraMap A O a₂ • x)
    have hc := hβ (c • x)
    have comm1 : algebraMap A O a₂ • c • x = c • algebraMap A O a₂ • x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    have comm2 : algebraMap A O a₁ • c • β x = c • algebraMap A O a₁ • β x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    refine ⟨w - z0 (c • x) + c • z0 x, ?_⟩
    rw [comm1, hw, smul_add, hnm] at hc
    have hx' : c • (m₁ • g (algebraMap A O a₂ • x)) = c • (algebraMap A O a₁ • β x + (n * m₁) • z0 x) := by
      rw [hβ x]
    rw [smul_add, smul_comm c m₁, smul_comm c (n * m₁)] at hx'
    rw [hx'] at hc
    rw [smul_sub, comm2, eq_sub_of_add_eq hc.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides (β y)).mpr hy
      have h := hβ y
      rw [hz, ← smul_add, ← hnm] at h
      have e := cancel m₁ hm _ _ h
      obtain ⟨v, hv⟩ := h2 _ _ e
      exact (ProjectionSandwichLength y).mp ⟨v, hv⟩
    · intro hy
      obtain ⟨v, hv⟩ := (ProjectionSandwichLength y).mpr hy
      apply memW1
      refine ⟨g v - z0 y, ?_⟩
      have h := hβ y
      rw [hv, map_nsmul, hnm] at h
      rw [smul_sub, eq_sub_of_add_eq h.symm]
  · intro x hx
    have hu : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • (algebraMap A O a₁ • x) = (n * m₁) • z := by
      intro c hc
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides _).mpr (hx c hc)
      exact ⟨z, by rw [smul_smul, ← Algebra.commutes a₁, ← smul_smul, hz]⟩
    obtain ⟨w, hw⟩ := hu _ hn2
    rw [map_natCast, Nat.cast_smul_eq_nsmul, mul_smul] at hw
    have hu1 := cancel n hn _ _ hw
    have hw2 : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • w = n • z := by
      intro c hc
      obtain ⟨z, hz⟩ := hu c hc
      rw [hu1, smul_comm (algebraMap A O c) m₁ w, ← hnm] at hz
      exact ⟨z, cancel m₁ hm _ _ hz⟩
    obtain ⟨y0, z0', hy0⟩ := DegreeKernelLowerBound w hw2
    obtain ⟨y1, z1, hy1⟩ := h3 y0
    obtain ⟨z2, hz2⟩ := h1 (algebraMap A O a₂) y1
    refine ⟨y1, memW1 _ ⟨z0' - algebraMap A O a₂ • z1 - z2 + z0 y1, ?_⟩⟩
    have hb := hβ y1
    rw [hz2, hy1] at hb
    simp only [smul_add] at hb
    rw [smul_comm (algebraMap A O a₂) n z1] at hb
    simp only [hnm] at hb
    rw [smul_sub, hu1, hy0, smul_add, hnm, eq_sub_of_add_eq hb.symm]
    simp only [smul_add, smul_sub]
    abel

theorem UpperTheory.Gal.FiniteEtaleModels.betaLat_holds :
    LatGen → BetaLat := by
  intro hL q _ D 𝔟₁ 𝔟₂ n m₁ a₁ a₂ hn hm hle G1 G2 g h1 h2 h3
  have cancel : ∀ k : ℕ, 0 < k → ∀ x y : D.La, k • x = k • y → x = y := by
    intro k hk x y h
    haveI := D.freeLa
    have h' : (k : ℤ) • (x - y) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (by exact_mod_cast hk.ne')
    · exact sub_eq_zero.mp h0
  obtain ⟨BaseTypeSubspacesMapOntoBothSides, PairingFactorsThroughPeriods⟩ := hL q D a₁ (n * m₁) 𝔟₁ (Nat.mul_pos hn hm) G1
  obtain ⟨ProjectionSandwichLength, DegreeKernelLowerBound⟩ := hL q D a₂ n 𝔟₂ hn G2
  obtain ⟨hn2, hc2⟩ := gen_facts G2
  obtain ⟨β, hadd, hlin, hker, honto, hmain⟩ :=
    reindex_lattice_of_ideals cancel 𝔟₁ 𝔟₂ (wSub D 𝔟₁ 1) (wSub D 𝔟₂ 1) n m₁ a₁ a₂ hn hm hle hn2 hc2
      BaseTypeSubspacesMapOntoBothSides PairingFactorsThroughPeriods ProjectionSandwichLength DegreeKernelLowerBound g h1 h2 h3
  exact ⟨β, ⟨hadd, hlin, hker, honto⟩, hmain⟩
