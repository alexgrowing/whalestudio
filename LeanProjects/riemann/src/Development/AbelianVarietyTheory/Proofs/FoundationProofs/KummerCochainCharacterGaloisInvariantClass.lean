import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfCharStatement
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kum_eq_of_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} (hN : 0 < N) {ζ θ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) (g : Ω ≃ₐ[K] Ω) (i : ZMod N) (hg : g θ = ζ ^ i.val * θ) :
    kum ζ θ g = i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hex : ∃ j : ZMod N, g θ = ζ ^ j.val * θ := ⟨i, hg⟩
  unfold kum
  rw [dif_pos hex]
  have h1 := hex.choose_spec
  have h2 : ζ ^ i.val = ζ ^ hex.choose.val := mul_right_cancel₀ hθ (hg.symm.trans h1)
  have h3 := (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)) h2
  exact (ZMod.val_injective N h3).symm

theorem eta_kummer_galoisInvariant : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix a b α β ha hb hα hβ η hη hcob
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  set E := IntermediateField.adjoin K ({α, β} : Set Ω) with hE
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hα; exact ha ((map_eq_zero _).mp hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hβ; exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨-, hαapp, hαmul, hαker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨-, hβapp, hβmul, hβker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  let x : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ α g)) (fun g h => by simp [hαmul, ofAdd_add])
  let y : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ β g)) (fun g h => by simp [hβmul, ofAdd_add])
  obtain ⟨-, hconj, hhom⟩ := GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary (Ω ≃ₐ[K] Ω) N x y η (fun g h => hcob g h)

  have memH : ∀ g : Ω ≃ₐ[K] Ω, g ∈ E.fixingSubgroup ↔ g α = α ∧ g β = β := by
    intro g
    constructor
    · intro hg
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg α
          (IntermediateField.subset_adjoin K _ (by simp)),
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg β
          (IntermediateField.subset_adjoin K _ (by simp))⟩
    · rintro ⟨h1, h2⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      | algebraMap r => exact g.commutes r
      | add u v _ _ hu hv => rw [map_add, hu, hv]
      | inv u _ hu => rw [map_inv₀, hu]
      | mul u v _ _ hu hv => rw [map_mul, hu, hv]
  have kα0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ α g = 0 := fun g hg => (hαker g).2 ((memH g).1 hg).1
  have kβ0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ β g = 0 := fun g hg => (hβker g).2 ((memH g).1 hg).2
  have hηhom : ∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, η (g * h) = η g + η h :=
    fun g hg h _ => hhom g h (kα0 g hg)
  obtain ⟨θ, hθ0, hθE, hθapp⟩ := GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom K Ω N ζ hN hζ hfix E η hη hηhom
  have hkθ : ∀ g ∈ E.fixingSubgroup, η g = kum ζ θ g := fun g hg =>
    (kum_eq_of_apply hN hζ hθ0 g (η g) (hθapp g hg)).symm
  refine ⟨θ, hθ0, hθE, hkθ, fun s => ?_⟩

  have hconjH : ∀ m ∈ E.fixingSubgroup, s⁻¹ * m * s ∈ E.fixingSubgroup ∧ η (s⁻¹ * m * s) = η m := by
    intro m hm
    obtain ⟨hmα, hmβ⟩ := (memH m).1 hm
    have hsα : m (s α) = s α := by
      rw [hαapp s, map_mul, map_pow, hfix m, hmα]
    have hsβ : m (s β) = s β := by
      rw [hβapp s, map_mul, map_pow, hfix m, hmβ]
    refine ⟨(memH _).2 ⟨?_, ?_⟩, ?_⟩
    · show s⁻¹ (m (s α)) = α
      rw [hsα]; exact s.symm_apply_apply α
    · show s⁻¹ (m (s β)) = β
      rw [hsβ]; exact s.symm_apply_apply β
    · have := hconj s⁻¹ m
      rw [inv_inv] at this
      rw [this]
      simp [x, y, kα0 m hm, kβ0 m hm]
  set u := s θ / θ with hu
  have hsθ0 : s θ ≠ 0 := by simpa using hθ0
  have hu0 : u ≠ 0 := div_ne_zero hsθ0 hθ0
  refine ⟨u, ?_, hu0, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro m hm
    obtain ⟨hmem, hηeq⟩ := hconjH m hm
    have h1 : m θ = ζ ^ (η m).val * θ := hθapp m hm
    have h2 : (s⁻¹ * m * s) θ = ζ ^ (η m).val * θ := by rw [← hηeq]; exact hθapp _ hmem
    have h3 : m (s θ) = ζ ^ (η m).val * s θ := by
      have : s ((s⁻¹ * m * s) θ) = m (s θ) := by
        show s (s⁻¹ (m (s θ))) = m (s θ)
        exact s.apply_symm_apply _
      rw [← this, h2, map_mul, map_pow, hfix s]
    have hz : ζ ^ (η m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [hu, map_div₀, h1, h3, mul_div_mul_left _ _ hz]
  · rw [map_pow, hu, div_pow, mul_div_cancel₀ _ (pow_ne_zero N hθ0)]

end GlobalTheory
