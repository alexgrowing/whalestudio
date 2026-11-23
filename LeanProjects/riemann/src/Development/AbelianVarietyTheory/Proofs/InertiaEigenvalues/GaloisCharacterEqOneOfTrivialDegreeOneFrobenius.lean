import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.FrobTrivChar

theorem eq_one_of_frob_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  classical
  intro E Ω _ _ _ _ _ l _ φ hφ hev
  have : IsGalois E Ω := {}
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  by_contra hg
  have hV : IsOpen {x : G E Ω | φ x ≠ 1} := isOpen_ne_fun hφ continuous_const
  have hn : (fun u : G E Ω => u * g) ⁻¹' {x : G E Ω | φ x ≠ 1} ∈ nhds (1 : G E Ω) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω _).1 hn
  have hgal : IsGalois E L := {}
  have hS := Filter.eventually_cofinite.1 hev
  obtain ⟨v, hv, hf, he, B, hB, -, σ, hσ, hU⟩ := GlobalTheory.Published.cheb_holds E Ω L.fixingSubgroup
    L.fixingSubgroup_isOpen ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g hS.toFinset
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  have h1 := hL hU
  simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_right] at h1
  exact h1 (hv hf he B σ hB hσ)

end GlobalTheory.FrobTrivChar
