import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def evL (H : Subgroup G) (ρ : Representation ℂ H W) (g : G) : cIndSpace H ρ →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype

theorem bump_right_inv {H : Subgroup G} {ρ : Representation ℂ H W} {K : Subgroup G} {v : W} {b : cIndSpace H ρ}
    (hb : IsBump H ρ K 1 v b) (g z : G) (hz : z ∈ K) : b.1.1.1 (g * z) = b.1.1.1 g := by
  by_cases h : ∃ a : H, ∃ x ∈ K, g = (a : G) * 1 * x
  · obtain ⟨a, x, hx, rfl⟩ := h
    rw [hb.1 a x hx, mul_assoc, hb.1 a (x * z) (mul_mem hx hz)]
  · rw [hb.2 g h, hb.2]
    rintro ⟨a, x, hx, e⟩
    exact h ⟨a, x * z⁻¹, mul_mem hx (inv_mem hz), by rw [← mul_assoc, ← e]; group⟩

theorem sum_translate {M : Type} [AddCommMonoid M] (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁) (φ : G → M)
    (hφ : ∀ g, ∀ z ∈ K₂, φ (g * z) = φ g) [Fintype (K₁ ⧸ K₂.subgroupOf K₁)] (y : K₁) :
    ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((y : G) * ((x.out : K₁) : G)) =
      ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((x.out : K₁) : G) := by
  have key : ∀ k : K₁, φ ((((k : K₁ ⧸ K₂.subgroupOf K₁).out : K₁)) : G) = φ (k : G) := by
    intro k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K₂.subgroupOf K₁) k
    rw [hh]
    exact hφ _ _ h.2
  calc ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((y : G) * ((x.out : K₁) : G))
      = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ (((MulAction.toPerm y x).out : K₁) : G) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have e : MulAction.toPerm y x = ((y * x.out : K₁) : K₁ ⧸ K₂.subgroupOf K₁) := by
          conv_lhs => rw [← QuotientGroup.out_eq' x]
          rfl
        rw [e, key]
        rfl
    _ = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((x.out : K₁) : G) :=
        Equiv.sum_comp (MulAction.toPerm y) (fun x : K₁ ⧸ K₂.subgroupOf K₁ => φ ((x.out : K₁) : G))

theorem bump_mem_of_bump {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁)
    (hK₁c : IsCompact (K₁ : Set G)) (hK₂o : IsOpen (K₂ : Set G)) (v : W)
    (hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v) (S : Submodule ℂ (cIndSpace H ρ))
    (hS : ∀ g, ∀ b ∈ S, cInd H ρ g b ∈ S) (b : cIndSpace H ρ) (hb : IsBump H ρ K₂ 1 v b) (hbS : b ∈ S)
    (B : cIndSpace H ρ) (hB : IsBump H ρ K₁ 1 v B) : B ∈ S := by
  classical
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c
  haveI : Finite (K₁ ⧸ K₂.subgroupOf K₁) :=
    Subgroup.quotient_finite_of_isOpen _ (hK₂o.preimage continuous_subtype_val)
  letI : Fintype (K₁ ⧸ K₂.subgroupOf K₁) := Fintype.ofFinite _
  set T : cIndSpace H ρ := ∑ x : K₁ ⧸ K₂.subgroupOf K₁, cInd H ρ ((x.out : K₁) : G) b with hT
  have hTS : T ∈ S := S.sum_mem fun x _ => hS _ _ hbS
  have hTv : ∀ g, T.1.1.1 g = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, b.1.1.1 (g * ((x.out : K₁) : G)) := by
    intro g
    have e : evL H ρ g T = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, evL H ρ g (cInd H ρ ((x.out : K₁) : G) b) := by
      rw [hT, map_sum]
    exact e
  have hTr : ∀ g, ∀ y ∈ K₁, T.1.1.1 (g * y) = T.1.1.1 g := by
    intro g y hy
    rw [hTv, hTv]
    have := sum_translate K₁ K₂ h₂₁ (fun u => b.1.1.1 (g * u))
      (fun u z hz => by
        show b.1.1.1 (g * (u * z)) = b.1.1.1 (g * u)
        rw [← mul_assoc]; exact bump_right_inv hb _ z hz) ⟨y, hy⟩
    simpa only [mul_assoc] using this
  let P : K₁ ⧸ K₂.subgroupOf K₁ → Prop := fun x => ∃ a : H, ∃ z ∈ K₂, ((x.out : K₁) : G) = (a : G) * 1 * z
  have hval : ∀ x, b.1.1.1 ((x.out : K₁) : G) = if P x then v else 0 := by
    intro x
    by_cases hx : P x
    · rw [if_pos hx]
      obtain ⟨a, z, hz, e⟩ := hx
      have ha : (a : G) ∈ K₁ := by
        have : (a : G) = ((x.out : K₁) : G) * z⁻¹ := by rw [e]; group
        rw [this]
        exact mul_mem (x.out).2 (inv_mem (h₂₁ hz))
      rw [e, hb.1 a z hz, hv a ha]
    · rw [if_neg hx]
      exact hb.2 _ hx
  set N : ℕ := (Finset.univ.filter P).card with hN
  have hT1 : T.1.1.1 1 = (N : ℂ) • v := by
    rw [hTv]
    simp only [one_mul, hval]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by
      rw [hN, Finset.card_ne_zero]
      refine ⟨((1 : K₁) : K₁ ⧸ K₂.subgroupOf K₁), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K₂.subgroupOf K₁) (1 : K₁)
      refine ⟨1, ((h : K₁) : G), h.2, ?_⟩
      rw [hh]
      simp
    exact_mod_cast this
  have hBT : B = (N : ℂ)⁻¹ • T := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    show B.1.1.1 g = (N : ℂ)⁻¹ • T.1.1.1 g
    by_cases hg : ∃ a : H, ∃ x ∈ K₁, g = (a : G) * 1 * x
    · obtain ⟨a, y, hy, rfl⟩ := hg
      have e1 : T.1.1.1 ((a : G) * 1 * y) = ρ a ((N : ℂ) • v) := by
        rw [hTr _ y hy, mul_one, ← hT1]
        have := T.1.1.2 a 1
        rwa [mul_one] at this
      rw [hB.1 a y hy, e1, map_smul, smul_smul, inv_mul_cancel₀ hN0, one_smul]
    · have e1 : T.1.1.1 g = 0 := by
        rw [hTv]
        refine Finset.sum_eq_zero fun x _ => hb.2 _ ?_
        rintro ⟨a, z, hz, e⟩
        refine hg ⟨a, z * ((x.out : K₁) : G)⁻¹, mul_mem (h₂₁ hz) (inv_mem (x.out).2), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hB.2 g hg, e1, smul_zero]
  rw [hBT]
  exact S.smul_mem _ hTS

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg

end
