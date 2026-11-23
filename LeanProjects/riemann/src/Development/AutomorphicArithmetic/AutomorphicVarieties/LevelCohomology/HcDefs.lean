import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.V.X

section Frame

variable {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M]
  [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)

def selF : Submodule k (H1 ρ) :=
  (⨅ v, LinearMap.ker (resH1 ρ (F.φ v) (F.hφ v))) ⊓
    ⨅ q, (H1ur (ρ.comp (F.ψ q)) (F.N q)).comap (resH1 ρ (F.ψ q) (F.hψ q))

def shaF : Submodule k (H2 ρ) :=
  (⨅ v, LinearMap.ker (resH2 ρ (F.φ v) (F.hφ v))) ⊓ ⨅ q, LinearMap.ker (resH2 ρ (F.ψ q) (F.hψ q))

end Frame

structure HcPublished : Prop where
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  pt : GlobalTheory.Published.PoitouTateNormalised

section Gal

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def cycK (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] : G ℚ Ω →* kˣ :=
  (Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) k).toMonoidHom).comp (cycMod ℚ Ω l 1)

variable {Ω}

def galFrame (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (v0 : T) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Alg.Frame (GS Ω SP) where
  T := T
  v0 := v0
  Gv v := Dec (F := ℚ) (pl v)
  φ v := locHom SP (pl v)
  hφ v := continuous_locHom SP (pl v)
  Q := Q
  Gq q := Dec (F := ℚ) (pl q)
  ψ q := locHom SP (pl q)
  hψ q := continuous_locHom SP (pl q)
  N q := (Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q))

structure GalData (l : ℕ) (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Prop where
  l_odd : l ≠ 2
  prime : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime
  disj : Disjoint T Q
  l_mem : l ∈ T
  mem : ∀ v, v ∈ SP ↔ ∃ p, (p ∈ T ∨ p ∈ Q) ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  isOver : ∀ p, p ∈ T ∨ p ∈ Q → (pl p).valuation (p : Ω) < 1
  idx : ∀ q ∈ Q, ¬ l ∣ K.relIndex (Ine (F := ℚ) (pl q))

def Van {k : Type} [Field k] (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)) (γ : G ℚ Ω →* kˣ) : Prop :=
  ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + (γ g : k) * z h) →
    (∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z g = 0) →
    (∀ v ∈ T, ∃ m, ∀ g ∈ Dec (F := ℚ) (pl v), z g = (γ g : k) * m - m) → ∃ m, ∀ g, z g = (γ g : k) * m - m

example (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    GalData l {v | ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} {l} ∅ (fun _ => A) ⊤ :=
  ⟨h2, by simpa using hl, by simp, by simp, by simp, by simpa using hA, by simp⟩

end Gal

end UpperTheory.V.X

end
