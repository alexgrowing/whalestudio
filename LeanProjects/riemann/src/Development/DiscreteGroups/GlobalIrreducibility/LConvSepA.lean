import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepF

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem delta_avg {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (L₁ L₂ : WT (m := m) ψ →ₗ[ℂ] ℂ) (h₁ : ∀ κ ∈ K, ∀ x, L₁ (rhoW ψ κ x) = L₁ x)
    (h₂ : ∀ κ ∈ K, ∀ x, L₂ (rhoW ψ κ x) = L₂ x) :
    L₁ (delta ψ K') * L₂ (delta ψ K) = L₁ (delta ψ K) * L₂ (delta ψ K') := by
  have hKc : CompactSpace K := isCompact_iff_compactSpace.1 hK.2.1
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  have : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  set P : WT (m := m) ψ := ∑ q : K ⧸ K'.subgroupOf K,
    rhoW ψ ((Quotient.out q : K) : GL (Fin m) k) (delta ψ K') with hP
  have hrep : ∀ a b : K, b⁻¹ * a ∈ K'.subgroupOf K →
      rhoW ψ (a : GL (Fin m) k) (delta ψ K') = rhoW ψ (b : GL (Fin m) k) (delta ψ K') := by
    intro a b hab
    have e : (a : GL (Fin m) k) = b * ((b⁻¹ * a : K) : GL (Fin m) k) := by simp
    rw [e, map_mul, Module.End.mul_apply, rhoW_delta (Subgroup.mem_subgroupOf.1 hab)]
  have hfix : ∀ κ ∈ K, rhoW ψ κ P = P := by
    intro κ hκ
    rw [hP, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨κ, hκ⟩ : K)) _ _ fun q => ?_
    rw [MulAction.toPerm_apply, ← Module.End.mul_apply, ← map_mul]
    have e : (QuotientGroup.mk (Quotient.out ((⟨κ, hκ⟩ : K) • q)) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk ((⟨κ, hκ⟩ : K) * Quotient.out q) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    have := hrep ((⟨κ, hκ⟩ : K) * Quotient.out q) (Quotient.out ((⟨κ, hκ⟩ : K) • q)) (QuotientGroup.eq.1 e)
    simpa using this
  have hL : ∀ L : WT (m := m) ψ →ₗ[ℂ] ℂ, (∀ κ ∈ K, ∀ x, L (rhoW ψ κ x) = L x) →
      L P = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) * L (delta ψ K') := by
    intro L hL
    rw [hP, map_sum, Finset.sum_congr rfl fun q _ => hL _ (Quotient.out q).2 _, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hs : ∀ g, (P : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ := by
    intro g hg
    rw [hP, Submodule.coe_sum, Finset.sum_apply] at hg
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    rw [rhoW_apply] at hq
    by_contra hno
    refine hq (delta_eq_zero ?_)
    rintro ⟨u, hu, κ', hκ', he⟩
    exact hno ⟨u, hu, κ' * ((Quotient.out q : K) : GL (Fin m) k)⁻¹,
      K.mul_mem (hle hκ') (K.inv_mem (Quotient.out q).2), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩
  obtain ⟨s, hPs⟩ : ∃ s : ℂ, P = s • delta ψ K := ⟨_, eq_smul_delta hK P hfix hs⟩
  have a1 := hL L₁ h₁
  have a2 := hL L₂ h₂
  rw [hPs, map_smul, smul_eq_mul] at a1 a2
  have c0 : (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ c0
  linear_combination (-L₂ (delta ψ K)) * a1 + L₁ (delta ψ K) * a2

def pairI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) : ℂ :=
  I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g

variable (ψ) in

def formI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pairI I)
    (fun x x' y => by
      simp only [pairI]
      rw [← map_add]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply, map_add]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]; ring)
    (fun x y y' => by
      simp only [pairI]
      rw [← map_add]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem formI_apply (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) :
    formI ψ I x y = I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := rfl

end DiscreteGroups.sglob.LConv

end
