import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffineDense

theorem sInf_minimalPrimes_eq_bot (R : Type) [CommRing R] [IsReduced R] :
    sInf (minimalPrimes R) = ⊥ := by
  rw [minimalPrimes, Ideal.sInf_minimalPrimes]
  exact nilradical_eq_zero R

theorem exists_minimal_ge_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : Ideal R) (hP : Disjoint (P : Set R) (nonZeroDivisors R)) :
    ∃ q ∈ minimalPrimes R, P ≤ q := by
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hsub : (P : Set R) ⊆ ⋃ i ∈ (↑t : Set (Ideal R)), ((fun I : Ideal R => I) i : Set R) := by
    intro a ha
    have hnz : a ∉ nonZeroDivisors R := fun h => Set.disjoint_left.1 hP ha h
    rw [mem_nonZeroDivisors_iff] at hnz
    push_neg at hnz
    obtain ⟨b, hba, hb⟩ : ∃ b, b * a = 0 ∧ b ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨x, hx, hx0⟩ := hnz (fun x hx => h x (by rw [mul_comm]; exact hx))
      exact hx0 (h x hx)
    have hb' : b ∉ sInf (minimalPrimes R) := by
      rw [sInf_minimalPrimes_eq_bot]; exact hb
    rw [Ideal.mem_sInf] at hb'
    push_neg at hb'
    obtain ⟨q, hq, hbq⟩ := hb'
    have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    have haq : a ∈ q := (hqp.mem_or_mem (hba ▸ q.zero_mem)).resolve_left hbq
    simp only [Set.mem_iUnion]
    exact ⟨q, by rw [ht]; exact hq, haq⟩
  obtain ⟨q, hqt, hPq⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i ∈ minimalPrimes R := by rw [← ht]; exact hi
    exact Ideal.minimalPrimes_isPrime this)).1 hsub
  exact ⟨q, by rw [← ht]; exact hqt, hPq⟩

theorem exists_annihilator_of_minimal {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : ∃ s ∉ q, ∀ a ∈ q, s * a = 0 := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  have hnle : ¬ (t.erase q).inf (fun I : Ideal R => I) ≤ q := by
    rw [hqp.inf_le']
    rintro ⟨i, hi, hiq⟩
    have him : i ∈ minimalPrimes R := by rw [← ht]; exact Finset.mem_of_mem_erase hi
    have : q ≤ i := hq.2 ⟨Ideal.minimalPrimes_isPrime him, bot_le⟩ hiq
    exact Finset.ne_of_mem_erase hi (le_antisymm hiq this)
  obtain ⟨s, hs, hsq⟩ := Set.not_subset.1 hnle
  refine ⟨s, hsq, fun a ha => ?_⟩
  have : s * a ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro I hI
    by_cases hIq : I = q
    · subst hIq; exact I.mul_mem_left s ha
    · have hIt : I ∈ t.erase q := Finset.mem_erase.2 ⟨hIq, by rw [← Finset.mem_coe, ht]; exact hI⟩
      exact I.mul_mem_right a (Finset.inf_le (f := fun I : Ideal R => I) hIt hs)
  rw [sInf_minimalPrimes_eq_bot] at this
  exact this

theorem mem_of_dense_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (D : Set (PrimeSpectrum R)) (hDo : IsOpen D) (hD : Dense D) (P : PrimeSpectrum R)
    (hP : Disjoint (P.asIdeal : Set R) (nonZeroDivisors R)) : P ∈ D := by
  obtain ⟨q, hq, hPq⟩ := exists_minimal_ge_of_disjoint P.asIdeal hP
  obtain ⟨s, hsq, hs⟩ := exists_annihilator_of_minimal q hq
  let Q : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  obtain ⟨Q', hQ', hQ'D⟩ := hD.inter_open_nonempty (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen s).isOpen ⟨Q, hsq⟩
  have hle : Q ≤ Q' := by
    intro a ha
    have h0 : s * a ∈ Q'.asIdeal := by rw [hs a ha]; exact Q'.asIdeal.zero_mem
    exact (Q'.isPrime.mem_or_mem h0).resolve_left hQ'
  have hQD : Q ∈ D := ((PrimeSpectrum.le_iff_specializes Q Q').1 hle).mem_open hDo hQ'D
  exact ((PrimeSpectrum.le_iff_specializes P Q).1 hPq).mem_open hDo hQD

end GlobalTheory.AffineDense

open GlobalTheory.AffineDense in

theorem GlobalTheory.affineOpen_injects_to_dense : ∀ (X : Scheme.{0}) [IsReduced X] [IsLocallyNoetherian X] (U : X.Opens), Dense (U : Set X) → ∀ (W : X.Opens) (hW : IsAffineOpen W), ∃ (K : Type) (_ : CommRing K) (ρ : Γ(X, W) →+* K), Function.Injective ρ ∧ ⊤ ≤ (spMap ρ ≫ (show Sp Γ(X, W) ⟶ X from hW.fromSpec)) ⁻¹ᵁ U := by
  intro X _ _ U hU W hW
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  refine ⟨Localization (nonZeroDivisors Γ(X, W)), inferInstance, algebraMap _ _,
    IsLocalization.injective _ le_rfl, ?_⟩
  intro x _
  have hD : Dense ((hW.fromSpec ⁻¹ᵁ U : (Spec Γ(X, W)).Opens) : Set (Spec Γ(X, W))) :=
    hU.preimage hW.fromSpec.isOpenEmbedding.isOpenMap
  have key := mem_of_dense_of_disjoint (R := Γ(X, W)) _ (hW.fromSpec ⁻¹ᵁ U).isOpen hD
    ((spMap (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))))).base x) ?_
  · exact key
  · rw [Set.disjoint_left]
    intro a ha hnzd
    have hu : IsUnit (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))) a) :=
      IsLocalization.map_units _ (⟨a, hnzd⟩ : nonZeroDivisors Γ(X, W))
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
