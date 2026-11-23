import Formalism.GaloisIrreducibility.NoSolvableOf

namespace Formalism.GaloisIrreducibility

open Module Polynomial

section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

lemma la_restrict_pow (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W)
    (n : ℕ) (v : W) : (((τ.restrict hτ) ^ n) v : V) = (τ ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.restrict_coe_apply, ih, pow_succ',
      Module.End.mul_apply]

lemma la_card_roots [IsAlgClosed K] [FiniteDimensional K V] (φ : Module.End K V) :
    (LinearMap.charpoly φ).roots.card = finrank K V := by
  rw [← LinearMap.charpoly_natDegree φ]
  exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))

end SlopeTestRemainingChoices

theorem lemmaAOf_statement : LemmaAOf := by
  classical
  unfold LemmaAOf LemmaA
  intro hOS hRR K V ι _ _ _ _ _ τ F q O I hF hO hroots W₁ W₂ hle h1τ h1F h2τ h2F

  obtain ⟨hA1, hA2⟩ := hRR K V τ F q hF W₂ h2τ h2F

  let g : W₂ →ₗ[K] W₂ := F.toLinearMap.restrict h2F
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply F.injective
    exact congrArg Subtype.val hxy
  let F₂ : W₂ ≃ₗ[K] W₂ := LinearEquiv.ofInjectiveEndo g hg
  have hF₂ : ∀ v, F₂ (τ.restrict h2τ v) = ((τ.restrict h2τ) ^ q) (F₂ v) := by
    intro v
    apply Subtype.ext
    rw [la_restrict_pow τ W₂ h2τ q (F₂ v)]
    exact hF (v : V)

  let W₁' : Submodule K W₂ := W₁.comap W₂.subtype
  have h1τ' : ∀ v ∈ W₁', τ.restrict h2τ v ∈ W₁' := fun v hv => h1τ (v : V) hv
  have h1F' : ∀ v ∈ W₁', F₂ v ∈ W₁' := fun v hv => h1F (v : V) hv
  obtain ⟨hB1, hB2⟩ := hRR K W₂ (τ.restrict h2τ) F₂ q hF₂ W₁' h1τ' h1F'
  have hc2 : (LinearMap.charpoly (τ.restrict h2τ)).roots.card = finrank K W₂ :=
    la_card_roots _
  have hc1 : (LinearMap.charpoly ((τ.restrict h2τ).restrict h1τ')).roots.card
      = finrank K W₁' := la_card_roots _
  have hW : finrank K W₁' = finrank K W₁ := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  set M₂ := (LinearMap.charpoly (τ.restrict h2τ)).roots with hM₂
  set M₁ := (LinearMap.charpoly ((τ.restrict h2τ).restrict h1τ')).roots with hM₁

  have hsplit : M₂ = M₁ + (M₂ - M₁) := (add_tsub_cancel_of_le hB1).symm
  have hmap : (M₂ - M₁).map (fun x : K => x ^ q) = M₂ - M₁ := by
    have h := congrArg (Multiset.map (fun x : K => x ^ q)) hsplit
    rw [Multiset.map_add, hB2, hA2] at h
    have h' : M₁ + (M₂ - M₁) = M₁ + Multiset.map (fun x : K => x ^ q) (M₂ - M₁) :=
      hsplit.symm.trans h
    exact (add_left_cancel h').symm
  have hsub : M₂ - M₁ ≤ ∑ i ∈ I, (O i).val := by
    rw [← hroots]
    exact tsub_le_self.trans hA1
  obtain ⟨J, hJ, hcard⟩ := hOS K ι (fun x : K => x ^ q) O I (M₂ - M₁) hO hsub hmap
  refine ⟨J, hJ, ?_⟩
  rw [← hcard, Multiset.card_sub hB1, hc2, hc1, hW]

end Formalism.GaloisIrreducibility
