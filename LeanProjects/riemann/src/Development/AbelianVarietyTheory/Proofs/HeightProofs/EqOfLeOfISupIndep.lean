import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.DegreeIdentityCharacter
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKroneckerCharIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumCompare

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

theorem pure_decomposition (X : CMObj H K ρ σ₁ p q) (b : Bool) (F : GenFib (X.A b).pol) :
    (∀ τ : 𝓞 E →+* 𝓞 K, latRank K (F.eigLat (X.A b).t.act τ) =
      open Classical in if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
    iSupIndep (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat (X.A b).t.act τ : Set (Fin F.P₀.g → K))) ∧
    ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat (X.A b).t.act τ : Set (Fin F.P₀.g → K)) = ⊤ ∧
    F.P₀.g = Module.finrank ℚ E / 2 := by
  cases b
  · obtain ⟨a, b, c, d, -⟩ := EigDec.eigen_decomposition E H K (-ρ) _ F 1 0 X.split
      (Test.hasType_neg X.ρ_sq X.typeM) (by rw [neg_sq, X.ρ_sq])
    exact ⟨a, b, c, by rw [F.fib.1]; simpa using d⟩
  · obtain ⟨a, b, c, d, -⟩ := EigDec.eigen_decomposition E H K ρ _ F 1 0 X.split X.typeP X.ρ_sq
    exact ⟨a, b, c, by rw [F.fib.1]; simpa using d⟩

def MultiplierNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K)
    (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (j : Fin p ⊕ Fin q) (s : K →+* ℂ) (τ : 𝓞 E →+* 𝓞 K),
    0 ≤ (s (τ (X.hh j) : K)).re

section Linear

variable {k V J : Type} [Field k] [AddCommGroup V] [Module k V]

theorem eq_of_le_of_iSupIndep {N W : J → Submodule k V} (hle : ∀ i, N i ≤ W i) (hW : iSupIndep W)
    (hN : ⨆ i, N i = ⊤) (i : J) : W i ≤ N i := by
  have h₁ : (⊤ : Submodule k V) = N i ⊔ ⨆ j, ⨆ _ : j ≠ i, N j := by rw [← hN, iSup_split_single N i]
  have h₂ : Disjoint (W i) (⨆ j, ⨆ _ : j ≠ i, N j) := (hW i).mono_right (iSup₂_mono fun j _ => hle j)
  have h₃ := sup_inf_assoc_of_le (⨆ j, ⨆ _ : j ≠ i, N j) (hle i)
  rw [← h₁, top_inf_eq, h₂.symm.eq_bot, sup_bot_eq] at h₃
  exact h₃.le

variable [FiniteDimensional k V] [Fintype J]

theorem indep_of_sum_le {N : J → Submodule k V} {n : J → ℕ} (h : ⨆ i, N i = ⊤) (hn : ∀ i, Module.finrank k (N i) ≤ n i)
    (hd : ∑ i, n i ≤ Module.finrank k V) : iSupIndep N ∧ ∀ i, Module.finrank k (N i) = n i := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have h₁ := LinearMap.finrank_le_finrank_of_surjective hs
  have h₂ : ∑ i, Module.finrank k (N i) ≤ ∑ i, n i := Finset.sum_le_sum fun i _ => hn i
  have he : Module.finrank k (DirectSum J fun i => N i) = Module.finrank k V := by
    rw [Module.finrank_directSum] at h₁ ⊢
    omega
  refine ⟨DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩, fun i => ?_⟩
  rw [Module.finrank_directSum] at he
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => hn i).1 (by omega) i (Finset.mem_univ _)

theorem sum_finrank_eq {N : J → Submodule k V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank k (N i) = Module.finrank k V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

end Linear

theorem ind_concl_iff (X : CMObj H K ρ σ₁ p q) (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) :
    (let N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
      ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K))
    (∀ x, N x ≤ FB.eigLat X.B.t.act x.2) ∧
    (∀ x, latRank K (N x) = open Classical in if x.2 H.rt = (if x.1.isLeft then ρ else -ρ) then 1 else 0) ∧
    (∀ j, Function.Injective (M j)) ∧
    iSupIndep (fun x => Submodule.span K (N x : Set (Fin FB.P₀.g → K))) ∧
    ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤) ↔
    ∀ τ : 𝓞 E →+* 𝓞 K,
      (∀ j : Fin p ⊕ Fin q, ∀ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, M j c ∈ FB.eigLat X.B.t.act τ) ∧
      (FB.eigLat X.B.t.act τ : Set (Fin FB.P₀.g → K)) ⊆
        Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c} := by
  classical
  set N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
    ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K)) with hN
  obtain ⟨-, hBi, hBt, hBg, -⟩ := EigDec.eigen_decomposition E H K ρ X.B FB p q X.split X.typeB X.ρ_sq
  have hset : ∀ τ : 𝓞 E →+* 𝓞 K,
      Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c} =
        ⨆ j, Submodule.span K (N (j, τ) : Set (Fin FB.P₀.g → K)) := fun τ => by
    rw [← Submodule.span_iUnion]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact exists_congr fun j => ⟨fun ⟨c, h, e⟩ => ⟨c, h, e.symm⟩, fun ⟨c, h, e⟩ => ⟨c, h, e.symm⟩⟩
  simp only [hset]
  refine ⟨fun ⟨h₁, _, _, _, h₅⟩ τ => ⟨fun j c hc => h₁ (j, τ) ⟨c, hc, rfl⟩, ?_⟩, fun h => ?_⟩
  · refine Submodule.subset_span.trans (eq_of_le_of_iSupIndep
      (N := fun τ => ⨆ j, Submodule.span K (N (j, τ) : Set (Fin FB.P₀.g → K)))
      (fun τ => iSup_le fun j => Submodule.span_mono (h₁ (j, τ))) hBi ?_ τ)
    rw [iSup_comm, ← h₅, iSup_prod]
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hA := fun b => pure_decomposition X b (FA b)
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, iSup_comm, eq_top_iff, ← hBt]
    exact iSup_mono fun τ => Submodule.span_le.2 (h τ).2
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    have : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := FB.fib.1.trans hBg
    simp [(hA _).2.2.2, this, mul_comm]
  obtain ⟨hi, hr⟩ := indep_of_sum_le (n := fun x : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) =>
    latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2)) htop
    (fun x => by rw [hspan]; exact Submodule.finrank_map_le _ _) (by
      rw [← hdim, Fintype.sum_prod_type]
      exact le_of_eq (Finset.sum_congr rfl fun j _ => sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1))
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le fun x => (hspan x).le.trans (LinearMap.map_le_range.trans (le_iSup (fun j => LinearMap.range (M j)) x.1))
  refine ⟨fun x => ?_, fun x => (hr x).trans ((hA _).1 _), fun j => ?_, hi, htop⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact (h x.2).1 x.1 c hc
  · have h₁ := (indep_of_sum_le hsur (fun j => LinearMap.finrank_range_le (M j)) hdim.le).2 j
    have := LinearMap.finrank_range_add_finrank_ker (M j)
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    omega

end GlobalTheory.CM.NumCompare
end
