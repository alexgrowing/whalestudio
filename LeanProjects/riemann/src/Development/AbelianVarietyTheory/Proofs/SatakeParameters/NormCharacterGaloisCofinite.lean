import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousResI
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open Pointwise

namespace GlobalTheory

theorem trivial_on_ext_of_frob_eq_normChar : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (η : HChar K), UpperTheory.V.Published.IsNormChar M η → ∀ χ : G K Ω →* ℂˣ, IsOpen (χ.ker : Set (G K Ω)) → (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v) → ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1 := by
  intro Ω _ K _ _ _ _ M _ _ _ _ _ _ η hη χ hχo hχ g hg
  classical
  let r : G M Ω →* G K Ω := AlgEquiv.restrictScalarsHom K
  have hr : Continuous r := GlobalTheory.WeilRes.continuous_res
  let u : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K)
  have hu : ∀ w : HeightOneSpectrum (𝓞 M), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hS := Filter.eventually_cofinite.1 hχ
  have hT₁ := Filter.eventually_cofinite.1 hη.2.2
  let T : Set (HeightOneSpectrum (𝓞 M)) :=
    {w | ¬ ∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1} ∪
      u ⁻¹' {v | ¬ ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v}
  have hT : T.Finite := hT₁.union (hS.preimage' (f := u) fun v _ => by
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩)
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := M) (Ω := Ω) hT
  let H : Subgroup (G M Ω) := (χ.comp r).ker
  have hHc : IsClosed (H : Set (G M Ω)) := H.isClosed_of_isOpen (by exact hχo.preimage hr)
  have hsub : {σ : G M Ω | ∃ w : HeightOneSpectrum (𝓞 M), w ∉ T ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆ H := by
    rintro σ ⟨w, hw, hd, B, hB, hσ⟩
    have hw1 : ∀ f : ℕ, normV w = normV (u w) ^ f → η.val (u w) ^ f = 1 := by
      by_contra h; exact hw (Or.inl h)
    have hw2 : ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A (u w) → IsFrob A (normV (u w)) σ →
        χ σ = η.val (u w) := by
      by_contra h; exact hw (Or.inr h)
    have hp : (Ideal.absNorm w.asIdeal).Prime :=
      ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified M).1 w).2 hd
    have hn : Ideal.absNorm (u w).asIdeal = Ideal.absNorm w.asIdeal := by
      haveI := hu w
      have h := Ideal.absNorm_pow_inertiaDeg (u w).asIdeal w.asIdeal
      have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
      rw [h1, pow_one] at h
      exact h
    have hnv : normV w = normV (u w) := hn.symm
    have hBv : IsPlaceOver B (u w) := fun x => by
      have e : algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) := by
        rw [IsScalarTower.algebraMap_apply K M Ω]; rfl
      rw [e]
      exact hB _
    have hrσ : IsFrob B (normV (u w)) (r σ) := by
      refine ⟨?_, fun x hx => ?_⟩
      · have h : σ • B = B := hσ.1
        show (σ.restrictScalars K) • B = B
        ext x
        conv_rhs => rw [← h]
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        rfl
      · rw [← hnv]; exact hσ.2 x hx
    have h1 : χ (r σ) = η.val (u w) := hw2 B (r σ) hBv hrσ
    have h2 : η.val (u w) ^ 1 = 1 := hw1 1 (by rw [pow_one]; exact hnv)
    rw [pow_one] at h2
    show χ (r σ) = 1
    rw [h1, h2]
  have hall : ∀ τ : G M Ω, τ ∈ H := fun τ => hHc.closure_subset_iff.2 hsub (hdense τ)
  let τ : G M Ω := { g.toRingEquiv with commutes' := hg }
  have hτ : r τ = g := AlgEquiv.ext fun _ => rfl
  have := hall τ
  show χ g = 1
  rw [← hτ]
  exact this

end GlobalTheory
