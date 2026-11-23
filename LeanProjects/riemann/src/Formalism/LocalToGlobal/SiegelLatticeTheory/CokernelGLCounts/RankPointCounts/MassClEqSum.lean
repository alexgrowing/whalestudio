import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RhoPf

open Formalism.L2.SG.TypedSets

section Abstract

variable {G : Type} [Group G]

theorem mem_map_conj (K : Subgroup G) (x a : G) :
    a ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * a * x ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem stab_eq_map (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom =
      (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
  ext a
  rw [Subgroup.mem_inf, mem_map_conj, mem_map_conj, Subgroup.mem_inf, mem_map_conj]
  have e1 : (γ * x * k)⁻¹ * a * (γ * x * k) = k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k := by group
  have e2 : x⁻¹ * (γ⁻¹ * a * γ) * x = k * (k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k) * k⁻¹ := by group
  constructor
  · rintro ⟨ha, hK⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) ha) hγ, ?_⟩
    rw [e1] at hK
    rw [e2]
    exact K.mul_mem (K.mul_mem hk hK) (K.inv_mem hk)
  · rintro ⟨ha, hK⟩
    refine ⟨?_, ?_⟩
    · have e3 : a = γ * (γ⁻¹ * a * γ) * γ⁻¹ := by group
      rw [e3]
      exact Γ.mul_mem (Γ.mul_mem hγ ha) (Γ.inv_mem hγ)
    · rw [e1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hK) hk

theorem card_conj_eq (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  rw [stab_eq_map Γ K x γ k hγ hk]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

theorem card_out_eq (Γ K : Subgroup G) (x : G) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out (DoubleCoset.mk Γ K x))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨γ, k, hγ, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
  rw [h]
  exact card_conj_eq Γ K x γ k hγ hk

end Abstract

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem massCl_comap (e : G' ≃* G) (Γ K : Subgroup G) :
    massCl (Γ.comap e.toMonoidHom) (K.comap e.toMonoidHom) = massCl Γ K := by
  set Γ' := Γ.comap e.toMonoidHom with hΓ'
  set K' := K.comap e.toMonoidHom with hK'
  have hstab : ∀ y : G', Nat.card ↥(Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom) := by
    intro y
    have hm : (Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom =
        Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom := by
      ext a
      rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj, mem_map_conj]
      simp [hΓ', hK', Subgroup.mem_comap, map_mul, map_inv]
    rw [← hm, Subgroup.card_map_of_injective e.injective]
  unfold massCl
  refine finsum_eq_of_bijective (fun c => DoubleCoset.mk Γ K (e (Quotient.out c))) ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (DoubleCoset.eq Γ K _ _).mp h
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    refine (DoubleCoset.eq Γ' K' _ _).mpr
      ⟨e.symm γ, by simpa [hΓ'] using hγ, e.symm k, by simpa [hK'] using hk, ?_⟩
    apply e.injective
    simp [map_mul, h2]
  · intro c
    obtain ⟨γ, k, hγ, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ' K' (e.symm (Quotient.out c))
    refine ⟨DoubleCoset.mk Γ' K' (e.symm (Quotient.out c)), ?_⟩
    show DoubleCoset.mk Γ K (e (Quotient.out (DoubleCoset.mk Γ' K' (e.symm (Quotient.out c))))) = c
    rw [hout]
    conv_rhs => rw [← Quotient.out_eq c]
    refine ((DoubleCoset.eq Γ K _ _).mpr ⟨e γ, hγ, e k, hk, ?_⟩).symm
    simp [map_mul]
  · intro c
    rw [card_out_eq, hstab]

end Transport

section Count

variable {G α : Type} [Group G]

theorem massCl_eq_sum (Γ K : Subgroup G) (S : Finset α) (ℓ : G → α) (w : α → ℝ)
    (hS : ∀ x, ℓ x ∈ S)
    (hrel : ∀ x y, ℓ x = ℓ y ↔ ∃ γ ∈ Γ, ∃ k ∈ K, y = γ * x * k)
    (hsurj : ∀ s ∈ S, ∃ x, ℓ x = s)
    (hw : ∀ x, ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℕ) : ℝ)⁻¹ = w (ℓ x)) :
    massCl Γ K = ∑ s ∈ S, w s := by
  unfold massCl
  have hout : ∀ x, ∃ γ ∈ Γ, ∃ k ∈ K, Quotient.out (DoubleCoset.mk Γ K x) = γ * x * k := by
    intro x
    obtain ⟨γ, k, hγ, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
    exact ⟨γ, hγ, k, hk, h⟩
  rw [← Finset.sum_coe_sort S w, ← finsum_eq_sum_of_fintype]
  refine finsum_eq_of_bijective (fun c => (⟨ℓ (Quotient.out c), hS _⟩ : {s // s ∈ S}))
    ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    have h' : ℓ (Quotient.out c1) = ℓ (Quotient.out c2) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (hrel _ _).mp h'
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    exact (DoubleCoset.eq Γ K _ _).mpr ⟨γ, hγ, k, hk, h2⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := hsurj s hs
    refine ⟨DoubleCoset.mk Γ K x, Subtype.ext ?_⟩
    obtain ⟨γ, hγ, k, hk, h⟩ := hout x
    exact ((hrel _ _).mpr ⟨γ, hγ, k, hk, h⟩).symm
  · intro c
    exact hw _

end Count

end Formalism.L2.SG.RhoPf
