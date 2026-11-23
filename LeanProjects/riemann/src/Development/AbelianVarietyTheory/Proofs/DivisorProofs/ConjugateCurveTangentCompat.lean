import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.ConjPt

theorem coords_conj : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair)
    (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (a a' : K),
    (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) →
    coords Λ₁ Ω₁ (io a') = (g : ℂ →+* ℂ) ∘ coords Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  obtain ⟨hΩ₀, hΩ₁, hfix, hL0, ⟨𝔞, h𝔞, hL1⟩, h2, h3, hval⟩ := hT
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hd : (t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := (hA _).2 hint
  have hmem𝔞 : a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ io '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ io '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : io a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : io a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  by_cases ha : io a ∈ Λ₀.lattice
  · have ha' : io a' ∈ Λ₁.lattice := by
      rw [h1, hmem𝔞]
      have := add_mem hd ((hone a).1 (h0.1 ha))
      rwa [sub_add_cancel] at this
    simp only [coords, if_pos ha, if_pos ha']
    ext i; fin_cases i <;> simp
  · have ha' : io a' ∉ Λ₁.lattice := by
      intro h
      apply ha
      rw [h0, hone]
      have := sub_mem (hmem𝔞.1 (h1.1 h)) hd
      rwa [sub_sub_cancel] at this
    obtain ⟨e2, e3⟩ := hval a a' ha hint
    simp only [coords, if_neg ha, if_neg ha']
    have e3' : g (Λ₀.derivWeierstrassP (io a) / (2 * Ω₀ ^ 3)) = Λ₁.derivWeierstrassP (io a') / (2 * Ω₁ ^ 3) := by
      rw [mul_comm, ← div_div, map_div₀, e3, map_ofNat, div_div, mul_comm]
    ext i; fin_cases i <;> simp [e2, e3']

end GlobalTheory.CMTorsion.ConjPt

namespace GlobalTheory.CMTorsion.ConjPt

theorem conj_pt : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT h a a' hint
  have e := coords_conj K io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  exact GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (by ext; simp) e _

end GlobalTheory.CMTorsion.ConjPt
