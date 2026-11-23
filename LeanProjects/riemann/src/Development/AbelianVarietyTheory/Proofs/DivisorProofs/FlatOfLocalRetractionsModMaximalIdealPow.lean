import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open IsLocalRing

namespace GlobalTheory

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

theorem isLocalHom_mk_maximalIdeal_pow_succ (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))),
    Ideal.Quotient.eq] at hc
  have h1 : a * c - 1 ∈ maximalIdeal A := Ideal.pow_le_self n.succ_ne_zero hc
  have h2 : a * c ∈ maximalIdeal A := Ideal.mul_mem_right _ _ hu
  have h3 : (1 : A) ∈ maximalIdeal A := by simpa using sub_mem h2 h1
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

theorem quotientMap_pow_bijective_of_retraction (φ : A →+* B) [IsLocalHom φ] (n : ℕ)
    (hle : maximalIdeal A ^ (n + 1) ≤ (maximalIdeal B ^ (n + 1)).comap φ)
    (ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1)) (hψ : ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ →
      g₁.comp φ = g₂.comp φ → g₁ = g₂) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
  haveI hA := isLocalHom_mk_maximalIdeal_pow_succ (A := A) n
  haveI hB := isLocalHom_mk_maximalIdeal_pow_succ (A := B) n
  have hψφ : ∀ a, ψ (φ a) = Ideal.Quotient.mk _ a := fun a => RingHom.congr_fun hψ a
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨φ a, hψφ a⟩
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self n.succ_ne_zero))
  haveI hψl : IsLocalHom ψ := IsLocalHom.of_surjective ψ hsurj
  haveI hφl : IsLocalHom (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk] at hx
    exact (IsUnit.of_map φ _ (IsUnit.of_map (Ideal.Quotient.mk _) _ hx)).map _
  have key := huniq (Ideal.Quotient.mk _)
    ((Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle).comp ψ) hB inferInstance (by
      ext a
      simp [hψφ])
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have h1 : maximalIdeal B ≤ ((maximalIdeal A).map
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))).comap ψ := by
      intro b hb
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ b)
      rw [Ideal.mem_comap, ← hc]
      refine Ideal.mem_map_of_mem _ fun hu => hb ?_
      exact IsUnit.of_map ψ _ (hc ▸ hu.map _)
    have h2 := pow_le_comap_pow_of_le h1 (n + 1) hx
    rwa [Ideal.mem_comap, ← Ideal.map_pow, Ideal.map_quotient_self, hψφ, Ideal.mem_bot] at h2
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨ψ b, (RingHom.congr_fun key b).symm⟩

end

theorem flat_of_retractions_mod_pow {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hex : ∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ →
      IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal B).comap φ := fun a ha => map_nonunit φ a ha
  have hbij : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) φ (pow_le_comap_pow_of_le hle n)) := by
    intro n
    cases n with
    | zero =>
      haveI : Subsingleton (A ⧸ maximalIdeal A ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      haveI : Subsingleton (B ⧸ maximalIdeal B ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      obtain ⟨ψ, hψ⟩ := hex n
      exact quotientMap_pow_bijective_of_retraction φ n _ ψ hψ (huniq n)
  refine ringHom_flat_of_flat_quotientMap_pow φ ?_ (maximalIdeal_le_jacobson _)
    (pow_le_comap_pow_of_le hle) fun n => RingHom.Flat.of_bijective (hbij n)
  refine le_antisymm (Ideal.map_le_of_le_comap hle)
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) fun y hy => ?_)
  obtain ⟨x, hx⟩ := (hbij 2).2 (Ideal.Quotient.mk _ y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
  have hxm : x ∈ maximalIdeal A := by
    have : φ x ∈ maximalIdeal B := by
      simpa using add_mem (Ideal.pow_le_self two_ne_zero hx) hy
    exact fun hu => this (hu.map φ)
  rw [show y = φ x - (φ x - y) by ring]
  refine sub_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hxm)) (Submodule.mem_sup_right ?_)
  rwa [smul_eq_mul, ← pow_two]

end GlobalTheory
