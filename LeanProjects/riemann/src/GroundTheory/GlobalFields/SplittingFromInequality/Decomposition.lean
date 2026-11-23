import Mathlib
import GroundTheory.GlobalFields.SplittingFromInequality.Galois
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import GroundTheory.LocalFields.UnramifiedGalois

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter Module AdeleBaseChange SemiLocal IntermediateField
open scoped Pointwise

noncomputable section

section FixedField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem card_stabilizer_fixedField_eq (H : Subgroup Gal(L/K)) (w : HeightOneSpectrum (𝓞 L))
    (hD : MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) [FiniteDimensional K L] :
    Nat.card (MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) =
      Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ ↦ ⟨(σ : Gal(L/fixedField H)).restrictScalars K, σ.2⟩) ⟨?_, ?_⟩)
  · intro σ τ h
    exact Subtype.ext (AlgEquiv.restrictScalars_injective K (congrArg Subtype.val h))
  · rintro ⟨τ, hτ⟩
    have hτH : τ ∈ fixingSubgroup (fixedField H) := (fixingSubgroup_fixedField H).symm ▸ hD hτ
    exact ⟨⟨fixingSubgroupEquiv (fixedField H) ⟨τ, hτH⟩, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)⟩

theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le (H : Subgroup Gal(L/K))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 (fixedField H)))
    (w : HeightOneSpectrum (𝓞 L)) [w'.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver w'.asIdeal]
    (hD : MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) :
    w'.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w'.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal w'.asIdeal v.asIdeal
  have h1 := card_decompositionGroup v w
  have h2 := card_decompositionGroup w' w
  rw [card_stabilizer_fixedField_eq H w hD] at h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) w'.asIdeal w.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 K) w'.asIdeal w.asIdeal, h2] at h1
  have hpos : 0 < w.asIdeal.ramificationIdx (𝓞 (fixedField H)) *
      w.asIdeal.inertiaDeg (𝓞 (fixedField H)) := by
    rw [← h2]
    exact Nat.card_pos
  have key : w'.asIdeal.ramificationIdx (𝓞 K) * w'.asIdeal.inertiaDeg (𝓞 K) *
      (w.asIdeal.ramificationIdx (𝓞 (fixedField H)) * w.asIdeal.inertiaDeg (𝓞 (fixedField H))) =
      1 * (w.asIdeal.ramificationIdx (𝓞 (fixedField H)) *
        w.asIdeal.inertiaDeg (𝓞 (fixedField H))) := by
    rw [one_mul]
    conv_rhs => rw [h1]
    ring
  exact mul_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos key)

theorem splitsCompletely_fixedField_of_stabilizer_le (H : Subgroup Gal(L/K))
    (v : HeightOneSpectrum (𝓞 K))
    (hD : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) :
    SplitsCompletely (fixedField H) v := by
  intro w' hw'
  obtain ⟨w⟩ := nonempty_placesOver L w'
  have : w.1.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.1.asIdeal w'.asIdeal v.asIdeal
  exact ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le H v w' w.1 (hD w.1 this)

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem below_smul (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) : below K (σ • w) = below K w :=
  (below_eq_iff (σ • w) (below K w)).2 (by rw [smul_asIdeal]; infer_instance)

end FixedField

section Generation

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem FirstInequality.closure_stabilizer_eq_top (hFI : FirstInequality.{u})
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    Subgroup.closure (⋃ (w : HeightOneSpectrum (𝓞 L)) (_ : below K w ∉ T),
      (MulAction.stabilizer Gal(L/K) w.asIdeal : Set Gal(L/K))) = ⊤ := by
  set S : Set Gal(L/K) := ⋃ (w : HeightOneSpectrum (𝓞 L)) (_ : below K w ∉ T),
    (MulAction.stabilizer Gal(L/K) w.asIdeal : Set Gal(L/K)) with hS
  set H := Subgroup.closure S
  have hconj : ∀ g : Gal(L/K), (MulAut.conj g).toMonoidHom '' S ⊆ S := by
    rintro g _ ⟨σ, hσ, rfl⟩
    obtain ⟨w, hw, hσ⟩ := Set.mem_iUnion₂.1 hσ
    refine Set.mem_iUnion₂.2 ⟨g • w, by rwa [below_smul], ?_⟩
    have hσ' : σ • w.asIdeal = w.asIdeal := hσ
    change (g * σ * g⁻¹) • (g • w).asIdeal = (g • w).asIdeal
    rw [smul_asIdeal, mul_smul, mul_smul, inv_smul_smul, hσ']
  have hH : H.Normal := ⟨fun n hn g ↦ by
    have : (MulAut.conj g).toMonoidHom n ∈ H.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rw [MonoidHom.map_closure] at this
    exact Subgroup.closure_mono (hconj g) this⟩
  have hsplit : ∀ v ∉ T, SplitsCompletely (fixedField H) v := fun v hv ↦
    splitsCompletely_fixedField_of_stabilizer_le H v fun w hw _ hσ ↦
      Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨w, by rwa [(below_eq_iff w v).2 hw], hσ⟩)
  have h1 := hFI.finrank_eq_one_of_splitsCompletely_of_finite_of_isGalois
    (L := fixedField H) hT hsplit
  rw [IntermediateField.finrank_eq_one_iff] at h1
  rw [← fixingSubgroup_fixedField H, h1, fixingSubgroup_bot]

end Generation

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open AdicLiesOver in

theorem stabilizer_eq_zpowers_arithFrobAt (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    MulAction.stabilizer Gal(L/K) w.asIdeal =
      Subgroup.zpowers (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) := by
  have h : GroundTheory.LocalField.ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1 := by
    rw [GroundTheory.LocalField.ramificationIndex, ramificationIdx_integer v w, he]
  have hfr : decompositionToLocal v w (arithFrobAtDecomposition w) =
      GroundTheory.LocalField.frobenius _ _ h :=
    (eq_decompositionToLocal_arithFrobAt v w he _
      (GroundTheory.LocalField.frobenius_sub_pow_mem_maximalIdeal _ _ h)).symm
  have htop : Subgroup.zpowers (arithFrobAtDecomposition (K := K) w) = ⊤ := by
    refine eq_top_iff.2 fun σ _ ↦ ?_
    have hmem : decompositionToLocal v w σ ∈
        (Subgroup.zpowers (arithFrobAtDecomposition (K := K) w)).map (decompositionToLocal v w) := by
      rw [MonoidHom.map_zpowers, hfr, GroundTheory.LocalField.zpowers_frobenius]
      exact Subgroup.mem_top _
    obtain ⟨τ, hτ, hτσ⟩ := hmem
    rwa [← decompositionToLocal_injective v w hτσ]
  refine le_antisymm (fun σ hσ ↦ ?_) ((Subgroup.zpowers_le).2
    (IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (htop ▸ Subgroup.mem_top (⟨σ, hσ⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal))
  have hk' := congrArg Subtype.val hk
  rw [Subgroup.coe_zpow] at hk'
  exact Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩

end Frobenius

section FrobeniusGeneration

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

end FrobeniusGeneration

end

end GroundTheory.Global
