import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_eq_bot_of_orderOf {Q : Type} [CommGroup Q] [Finite Q] (χ : Q →* ℂˣ)
    (h : orderOf χ = Nat.card Q) : χ.ker = ⊥ := by
  have h1 : χ ^ χ.ker.index = 1 := by
    ext x
    have : x ^ χ.ker.index ∈ χ.ker := Subgroup.pow_index_mem _ _
    rw [MonoidHom.mem_ker, map_pow] at this
    simp [MonoidHom.pow_apply, this]
  have h2 : Nat.card Q ∣ χ.ker.index := h ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : χ.ker.index = Nat.card Q := Nat.dvd_antisymm (Subgroup.index_dvd_card _) h2
  have h4 := Subgroup.card_mul_index χ.ker
  rw [h3] at h4
  have h5 : Nat.card χ.ker = 1 := by
    have hp : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp (by rw [h4, one_mul])
  exact Subgroup.card_eq_one.1 h5

open Classical in
private theorem totient_le_card_ker {Γ : Type} [CommGroup Γ] [Finite Γ] [Fintype (Γ →* ℂˣ)] (H : Subgroup Γ)
    (hH : IsCyclic (Γ ⧸ H)) :
    Nat.totient H.index ≤ (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card := by
  haveI : NeZero (Monoid.exponent (Γ ⧸ H)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Γ ⧸ H) ℂ
  haveI : Finite ((Γ ⧸ H) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype ((Γ ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ((Γ ⧸ H) →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hc : Fintype.card ((Γ ⧸ H) →* ℂˣ) = H.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]; rfl
  rw [← IsCyclic.card_orderOf_eq_totient (α := (Γ ⧸ H) →* ℂˣ) (d := H.index) (hc ▸ dvd_rfl)]
  refine Finset.card_le_card_of_injOn (fun χ => χ.comp (QuotientGroup.mk' H)) ?_ ?_
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
    have := ker_eq_bot_of_orderOf χ hχ
    rw [← MonoidHom.comap_ker, this, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · intro a _ b _ hab
    exact QuotientGroup.monoidHom_ext _ hab

theorem UpperTheory.V.HV.orbSum :
    ∀ (Γ : Type) [CommGroup Γ] [Finite Γ] (T : Finset (Subgroup Γ)), (∀ H ∈ T, IsCyclic (Γ ⧸ H)) → ∑ H ∈ T, Nat.totient H.index ≤ Nat.card Γ := by
  intro Γ _ _ T hT
  classical
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Γ ℂ
  haveI : Finite (Γ →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  calc ∑ H ∈ T, Nat.totient H.index
      ≤ ∑ H ∈ T, (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card :=
        Finset.sum_le_sum fun H hH => by convert totient_le_card_ker H (hT H hH)
    _ = (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker ∈ T).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ Fintype.card (Γ →* ℂˣ) := Finset.card_le_univ _
    _ = Nat.card Γ := by rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]
