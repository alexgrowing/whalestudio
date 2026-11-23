import Mathlib

namespace GlobalTheory

open Subgroup

namespace UnfoldSemidirect

theorem mem_map_conj_iff {G : Type} [Group G] (K : Subgroup G) (g p : G) :
    p ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * p * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end UnfoldSemidirect

open UnfoldSemidirect in

theorem relIndex_unfold_semidirect : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hsec hu hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hcond q X
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  have hsinj : Function.Injective s := fun a b h => by
    have := congrArg π h
    rwa [hsec, hsec] at this
  have key : ∀ r : M, (s q * u X)⁻¹ * s (q * r * q⁻¹) * (s q * u X) = (u X)⁻¹ * s r * u X := by
    intro r; simp only [map_mul, map_inv]; group
  have hπc : ∀ r : M, π ((u X)⁻¹ * s r * u X) = r := by
    intro r; simp [map_mul, map_inv, hπu, hsec]
  have hCP' : CP = CM.map s := by
    ext p; rw [hCP p, Subgroup.mem_map]
  have hH : TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom
      = ((TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map
          (MulAut.conj q).toMonoidHom).map s := by
    ext p
    rw [Subgroup.mem_inf, mem_map_conj_iff, hTP p, Subgroup.mem_map]
    simp only [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hk⟩
      have hk' : (u X)⁻¹ * s (q⁻¹ * t * q) * u X ∈ KP := by
        rw [← key]; simpa [mul_assoc] using hk
      refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · simpa [mul_assoc] using ht
      · have h1 := hπK _ hk'
        rwa [hπc] at h1
      · simpa using hk'
    · rintro ⟨t, ⟨⟨hr1, hr2⟩, hr3⟩, rfl⟩
      refine ⟨⟨t, by simpa [mul_assoc] using hr1, rfl⟩, ?_⟩
      have := key (q⁻¹ * t * q)
      have e : q * (q⁻¹ * t * q) * q⁻¹ = t := by group
      rw [e] at this
      rw [this]; exact hr3
  have hSq : TM ⊓ KM.map (MulAut.conj q).toMonoidHom
      = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom := by
    ext p
    simp only [Subgroup.mem_inf, mem_map_conj_iff, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
  have hle1 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map (MulAut.conj q).toMonoidHom
        ≤ (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom :=
    Subgroup.map_mono inf_le_left
  have hle2 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom ≤ CM := by
    rw [← hSq]; exact hcond q
  rw [hH, hCP', Subgroup.relIndex_map_map_of_injective _ _ hsinj,
    ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj q).injective, ← hSq, mul_comm]

end GlobalTheory
