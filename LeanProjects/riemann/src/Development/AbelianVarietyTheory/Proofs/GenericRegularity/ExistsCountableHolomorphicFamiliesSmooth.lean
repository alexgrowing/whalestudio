import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
open Topology Filter

namespace GlobalTheory.SmoothPointCover

theorem exists_family_near (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ) (h₀ : φ₀.comp (algebraMap K A) = σ) :
    ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (U : Set (A → ℂ)), U ∈ 𝓝 (φ₀ : A → ℂ) ∧
      IsOpen B ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ) ∧
      (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧
      (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (ψ : A → ℂ) ∈ U → ∃ b ∈ B, φ b = ψ) ∧
      ∀ b ∈ B, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ b' a ≠ 0 := by
  classical
  obtain ⟨m, s, B, φ, S, ε, hB, hε, hφ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family K A σ φ₀ h₀
  let U : Set (A → ℂ) := {f | ∀ a ∈ S, ‖f a - φ₀ a‖ < ε}
  have hU : IsOpen U := by
    have : U = ⋂ a ∈ S, {f : A → ℂ | ‖f a - φ₀ a‖ < ε} := by
      ext f; simp [U]
    rw [this]
    exact isOpen_biInter_finset fun a _ => isOpen_lt (by fun_prop) continuous_const
  have hc : ContinuousOn (fun b => (φ b : A → ℂ)) B := continuousOn_pi.2 fun a => (hd a).continuousOn
  refine ⟨m, B ∩ (fun b => (φ b : A → ℂ)) ⁻¹' U, φ, U, hU.mem_nhds (fun a _ => by simpa using hε),
    hc.isOpen_inter_preimage hB hU, fun b hb => (hφ b hb.1).1, fun a => (hd a).mono Set.inter_subset_left,
    fun ψ hψ hψU => ?_, fun b hb a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := hnear ψ hψ hψU
    refine ⟨_, ⟨h1, ?_⟩, h2⟩
    rw [Set.mem_preimage, h2]
    exact hψU
  · rw [Filter.frequently_iff]
    intro V hV
    have hW : U ∩ (fun f : A → ℂ => fun i => f (s i)) ⁻¹' V ∈ 𝓝 (φ b : A → ℂ) := by
      refine Filter.inter_mem (hU.mem_nhds hb.2) ?_
      have hcs : Continuous (fun f : A → ℂ => fun i => f (s i)) := by fun_prop
      refine hcs.continuousAt.preimage_mem_nhds ?_
      have : (fun i => φ b (s i)) = b := funext (hφ b hb.1).2
      simpa only [this] using hV
    obtain ⟨S', δ, hδ, hS'⟩ := GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds hW
    obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near K A (FractionRing A) σ (φ b)
      (hφ b hb.1).1 S' δ hδ
    let ρ : A →+* ℂ := P.comp (algebraMap A (FractionRing A))
    have hρ : ρ.comp (algebraMap K A) = σ := RingHom.ext fun a => RingHom.congr_fun hP a
    obtain ⟨h3, h4⟩ := hS' ρ hPε
    refine ⟨_, h4, ?_⟩
    have h5 := (hnear ρ hρ h3).2
    change φ (fun i => ρ (s i)) a ≠ 0
    rw [h5]
    exact (map_ne_zero_iff ρ (P.injective.comp (IsFractionRing.injective A (FractionRing A)))).2 ha

theorem exists_countable_families : ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ), ∃ (ι : Type) (_ : Countable ι) (m : ι → ℕ) (B : ∀ i, Set (Fin (m i) → ℂ)) (φ : ∀ i, (Fin (m i) → ℂ) → (A →+* ℂ)), (∀ i, IsOpen (B i)) ∧ (∀ i, ∀ b ∈ B i, (φ i b).comp (algebraMap K A) = σ) ∧ (∀ i (a : A), DifferentiableOn ℂ (fun b => φ i b a) (B i)) ∧ (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → ∃ i, ∃ b ∈ B i, φ i b = ψ) ∧ ∀ i, ∀ b ∈ B i, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ i b' a ≠ 0 := by
  intro K A _ _ _ _ _ _ σ
  haveI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  haveI : Countable A := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K A)
    haveI : Countable (MvPolynomial (Fin n) K) := ReciprocityTheory.ChartRestriction.G.T0.NPB.countable_mvPoly
    exact hf.countable
  let X := {ψ : A →+* ℂ // ψ.comp (algebraMap K A) = σ}
  letI : TopologicalSpace X := TopologicalSpace.induced (fun ψ => (ψ.1 : A → ℂ)) inferInstance
  haveI : SecondCountableTopology X := TopologicalSpace.secondCountableTopology_induced X (A → ℂ) _
  choose m B φ U hU hB hσ hd hcov hne using fun x : X => exists_family_near K A σ x.1 x.2
  obtain ⟨t, ht, hcv⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x : X => (fun ψ : X => (ψ.1 : A → ℂ)) ⁻¹' U x)
    (fun x => continuous_induced_dom.continuousAt.preimage_mem_nhds (hU x))
  refine ⟨t, ht.to_subtype, fun i => m i.1, fun i => B i.1, fun i => φ i.1, fun i => hB i.1, fun i => hσ i.1,
    fun i => hd i.1, fun ψ hψ => ?_, fun i => hne i.1⟩
  have : (⟨ψ, hψ⟩ : X) ∈ ⋃ x ∈ t, (fun ψ : X => (ψ.1 : A → ℂ)) ⁻¹' U x := by rw [hcv]; trivial
  obtain ⟨x, hx, hψx⟩ := Set.mem_iUnion₂.1 this
  exact ⟨⟨x, hx⟩, hcov x ψ hψ hψx⟩

end GlobalTheory.SmoothPointCover
