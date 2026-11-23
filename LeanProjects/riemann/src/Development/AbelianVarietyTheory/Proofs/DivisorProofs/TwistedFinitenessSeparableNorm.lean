import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigKQMemIntKQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerNormInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFixedCosetDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormFixedDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCentralizerCommutativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFinitelyGeneratedModOpenStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL

theorem twFin_generic : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    (∀ a ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, ∀ b ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, a * b = b * a) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
      Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ≤
        Subgroup.closure ((G : Set H) ∪ ((Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ⊓ K₀ : Subgroup H) : Set H))) →
    GlobalTheory.TwFin.TwFin θ K₀ δ (GlobalTheory.LKMid.nrmG θ r δ) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm hZc hfg
  obtain ⟨hτZ, hτr⟩ := GlobalTheory.T.twisted_centralizer_norm_invariant θ δ r hr hθr
  obtain ⟨U, hUZ, hUK, hUτ, hUfg, hUcov⟩ :=
    GlobalTheory.T.twisted_norm_fixed_decomposition θ K₀ δ r hr hθr hθK hcomm _ hτZ hτr hfg
  intro E
  choose! F hF using hUcov
  obtain ⟨S, hS⟩ := GlobalTheory.T.twisted_fixed_coset_decomposition _ U ((MulAut.conj δ).toMonoidHom.comp θ) r hr hτZ hτr hZc hUZ hUτ hUfg
    (E.biUnion fun e => F e δ⁻¹)
  refine ⟨S, ?_⟩
  intro t htN hE
  obtain ⟨e, he, k, hk, hek⟩ := hE
  have htZ : t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact htN.symm
  have hτt : ((MulAut.conj δ).toMonoidHom.comp θ) t = δ * θ t * δ⁻¹ := rfl
  have hc : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ htZ) (hτZ t htZ)
  have hc' : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t = e * k * δ⁻¹ := by
    rw [hτt, ← mul_assoc, ← mul_assoc, hek]
  obtain ⟨f, hf, u, hu, hfu⟩ := hF e δ⁻¹ _ hc k hk hc'
  obtain ⟨b, -, hbτ, s, hs, u', hu', hbt⟩ :=
    hS t htZ ⟨f, Finset.mem_biUnion.2 ⟨e, he, hf⟩, u, hu, hfu⟩
  refine ⟨b, ?_, s, hs, u', hUK hu', hbt⟩
  change b * δ = δ * θ b
  have h1 : δ * θ b * δ⁻¹ = b := hbτ
  calc b * δ = δ * θ b * δ⁻¹ * δ := by rw [h1]
    _ = δ * θ b := by rw [inv_mul_cancel_right]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  intro p _ K hK n r hr δ hsep
  haveI := hK
  exact twFin_generic (sigRes p K n r) (Kres p K n r) δ r hr (sigRes_iterate_eq_self p K n r hr)
    (sigRes_mem_Kres p K n r) (fun g => GlobalTheory.HeckeP.Kres_commensurable p K n r hr g)
    (GlobalTheory.T.separable_centralizer_commutative p K hK n r hr _ hsep) (GlobalTheory.T.centralizer_finitely_generated_mod_open p K hK n r hr _ hsep)

end GlobalTheory.TwFinGL
