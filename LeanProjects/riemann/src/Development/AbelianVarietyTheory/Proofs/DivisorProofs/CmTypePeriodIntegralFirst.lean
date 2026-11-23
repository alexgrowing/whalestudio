import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.EigLineSum

theorem ringHom_eq_of_eq_on_orderC {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    {c : Ideal (OF E)} (hc : c ≠ ⊥) {σ σ' : E →+* K} (h : ∀ a : orderC c, σ a = σ' a) : σ = σ' := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set b' : 𝓞 E := algebraMap (OF E) (𝓞 E) b with hb'
  have hb'0 : algebraMap (𝓞 E) E b' ≠ 0 := by
    have : algebraMap (𝓞 E) E b' = algebraMap (OF E) E b := rfl
    rw [this]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hb0
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (b' * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨b' * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), rfl⟩)
  have hb'mem : algebraMap (𝓞 E) E b' ∈ orderC c := by simpa using hmem 1
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun z => ?_)
  have h1 : σ (algebraMap (𝓞 E) E (b' * z)) = σ' (algebraMap (𝓞 E) E (b' * z)) := h ⟨_, hmem z⟩
  have h2 : σ (algebraMap (𝓞 E) E b') = σ' (algebraMap (𝓞 E) E b') := h ⟨_, hb'mem⟩
  have h3 : σ (algebraMap (𝓞 E) E b') ≠ 0 := (map_ne_zero σ).2 hb'0
  simp only [map_mul] at h1
  rw [h2] at h1 h3
  simpa using mul_left_cancel₀ h3 h1

theorem eigK_isInternal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) := by
  intro E _ _ _ c hc l _ O _ _ _ _ K _ _ _ _ hcard D _ _ I _ φ _ H _ _ ρ Fil B hL
  obtain ⟨hfree, hfin, hrank, hline, -⟩ := hL
  let f : orderC c → Module.End K (K ⊗[O] H) := fun a => (ρ a).baseChange K
  have hcomm : ∀ a b, Commute (f a) (f b) := fun a b => by
    show (ρ a).baseChange K * (ρ b).baseChange K = (ρ b).baseChange K * (ρ a).baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have hind0 := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hinj : Function.Injective (fun σ : E →+* K => fun a : orderC c => σ a) := fun σ σ' h =>
    ringHom_eq_of_eq_on_orderC hc (fun a => congrFun h a)
  have hind : iSupIndep (fun σ : E →+* K => eigK ρ σ) :=
    (hind0.comp hinj).mono fun σ => iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  haveI := Fintype.ofFinite (E →+* K)
  have htot : Module.finrank K (K ⊗[O] H) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, hrank]
  have hinjD : Function.Injective (DirectSum.coeLinearMap (fun σ : E →+* K => eigK ρ σ)) :=
    hind.dfinsupp_lsum_injective
  have hdim : Module.finrank K (DirectSum (E →+* K) fun σ => eigK ρ σ) = Module.finrank K (K ⊗[O] H) := by
    rw [Module.finrank_directSum, htot, ← hcard, Nat.card_eq_fintype_card]
    simp [hline]
  exact ⟨hinjD, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinjD⟩

end GlobalTheory.EigLineSum
