import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.AutomorphicL2Unitary (LeftInv)

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem ratPts_inf_subgroupOf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) :
    (ratPts σ J ⊓ P).subgroupOf N = (ratPts σ J).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNP x.2⟩⟩

theorem isConstTermOn_iff_ratPts_inf {N P : Subgroup (GAd σ J)} [LocallyCompactSpace N] (hNP : N ≤ P)
    (hc : Cocompact (ratPts σ J) N) {φ c : GAd σ J → ℂ} (hφ : LeftInv (ratPts σ J ⊓ P) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J ⊓ P) N φ := by
  have e := ratPts_inf_subgroupOf (σ := σ) (J := J) hNP
  constructor
  · intro h
    obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
    funext g
    rw [h μ 𝓕 h1 h2 h3 g, GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g]
  · rintro rfl μ 𝓕 h1 h2 h3 g
    exact GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g

theorem cocompact_ratPts_inf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) (hc : Cocompact (ratPts σ J) N) :
    Cocompact (ratPts σ J ⊓ P) N := by
  unfold Cocompact
  rw [ratPts_inf_subgroupOf hNP]
  exact hc

section Witt

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem locallyCompact_unip (S : Finset (Fin r)) : LocallyCompactSpace (unip σ J X S) :=
  (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unip_std (S : Finset (Fin r)) : Cocompact (ratPts σ J) (unip σ J X S) := by
  by_cases hS0 : S = ∅
  · subst hS0
    refine ⟨{1}, isCompact_singleton, fun u => ⟨u⁻¹, ?_, by simp⟩⟩
    have hu : (u : GAd σ J) = 1 := Subgroup.mem_bot.1 (le_of_eq (unip_empty (σ := σ) (J := J) (X := X)) u.2)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv, hu, inv_one]
    exact one_mem _
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  rw [GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW S m hm hm']
  exact cocompact_unipFlag hJ (sigma_sigma h) (isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ m.2) _

theorem conj_mem_unip_of_subset {S T : Finset (Fin r)} (hTS : T ⊆ S) {p u : GAd σ J} (hp : p ∈ unip σ J X S)
    (hu : u ∈ unip σ J X T) : p * u * p⁻¹ ∈ unip σ J X T := by
  by_cases hT0 : T = ∅
  · subst hT0
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eT := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW T m hm hm'
  rw [eT] at hu ⊢
  exact conj_mem_unipFlag hJ hσ (isIsoCols_of_isWittFrame hW hσ hJ m.2) _
    (GlobalTheory.ConstTrans.unip_le_parFlag F E σ h n J hJ r X Y hW S T m hTS hm hm' hp) hu

theorem constAlong_cocompact_unique_stages :
    (∀ S : Finset (Fin r), Cocompact (ratPts σ J) (unip σ J X S) ∧
      ∃ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ S T : Finset (Fin r), T ⊆ S → unip σ J X T ≤ unip σ J X S ∧ levi σ J X Y S ≤ levi σ J X Y T) ∧
    (∀ (S : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), IsConstAlong σ J X S φ c → IsConstAlong σ J X S φ c' → c = c') ∧
    (∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      ∃ c, IsConstAlong σ J X S φ c) ∧
    (∀ (S T : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), T ⊆ S → Continuous φ →
      (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      IsConstAlong σ J X T φ c → IsConstAlong σ J X S c c' → IsConstAlong σ J X S φ c') := by
  refine ⟨fun S => ?_, fun S T hTS => ⟨unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS, ?_⟩,
    fun S φ c c' h1 h2 => ?_, fun S φ hφ => ?_, fun S T φ c c' hTS hφc hφ hc hc' => ?_⟩
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨cocompact_unip_std h hJ hW S, exists_mass_one (cocompact_unip_std h hJ hW S)⟩
  · intro g hg
    simp only [levi, Subgroup.mem_iInf] at hg ⊢
    exact fun k hk => hg k (hTS hk)
  · haveI := locallyCompact_unip h hJ hW S
    exact IsConstTermOn.unique (cocompact_unip_std h hJ hW S) h1 h2
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨_, isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 hγ.2 g⟩
  · haveI := locallyCompact_unip h hJ hW S
    haveI := locallyCompact_unip h hJ hW T
    have hle : unip σ J X T ≤ unip σ J X S := unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS
    have cS := cocompact_unip_std h hJ hW S
    have cT := cocompact_unip_std h hJ hW T
    have hfΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) φ := fun γ hγ g => hφ γ hγ.1 hγ.2 g
    have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T :=
      fun p hp u hu => conj_mem_unip_of_subset h hJ hW hTS hp hu
    have hc0 : c = constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ :=
      (isConstTermOn_iff_ratPts_inf hle cT hfΓ).1 hc
    subst hc0
    have hcΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) :=
      fun γ hγ g => GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hfΓ hγ
        (fun m => ⟨hnorm _ hγ.2 m, fun hm => by simpa [mul_assoc] using hnorm _ (inv_mem hγ.2) _ hm⟩) g
    have st : constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) φ =
        constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S)
          (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) := funext fun x =>
      GlobalTheory.Cusp.Stages.constTermOn_stages (GAd σ J) (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) (unip σ J X T) hle hnorm
        (cocompact_ratPts_inf le_rfl cS) (cocompact_ratPts_inf hle cT) φ hfΓ hφc x
    change IsConstTermOn σ J (unip σ J X S) _ c' at hc'
    change IsConstTermOn σ J (unip σ J X S) φ c'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hcΓ] at hc'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hfΓ, st]
    exact hc'

end Witt

end GlobalTheory.StdPar

end
