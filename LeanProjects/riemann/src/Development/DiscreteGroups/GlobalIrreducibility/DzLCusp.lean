import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
import Development.DiscreteGroups.GlobalIrreducibility.DzLcPerm
import Development.DiscreteGroups.GlobalIrreducibility.DzLcIso
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut

noncomputable section

open GlobalTheory.GLq GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.LocLanglands
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem twKer_twoBlocks_eq_top (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n a : ℕ} (h0 : 0 < a) (ha : a < n)
    (τ : FDRep ℂ (Gn g n)) (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 = ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hs
  have hgen : ∀ x : GL (Fin n) k, x ∈ GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) → ∀ v,
      σ.ρ x v - v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro x hx v
    refine Submodule.subset_span ⟨⟨x, hx⟩, v, ?_⟩
    simp
  have hφT : ∀ w, φ w ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro w
    have hfin := sum_unip_eq_zero τ hτ h0 ha
    have key : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        φ w - φ (τ.ρ (u : Gn g n) w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
      intro u
      obtain ⟨κ, hred, hmem⟩ := exists_lift i (u : Gn g n) u.2
      have h1 := hφ κ w
      rw [hred] at h1
      rw [h1, ← neg_sub]
      exact Submodule.neg_mem _ (hgen _ hmem (φ w))
    have hsum : ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        (φ w - φ (τ.ρ (u : Gn g n) w)) =
          (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) • φ w := by
      rw [Finset.sum_sub_distrib, ← map_sum φ (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n) w),
        ← LinearMap.sum_apply Finset.univ
          (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n)) w, hfin, LinearMap.zero_apply, map_zero,
        sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hc : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hmem := Submodule.sum_mem _ fun u (_ : u ∈ Finset.univ) => key u
    rw [hsum] at hmem
    have := Submodule.smul_mem _
      (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ (h : GL (Fin n) k) (w : τ),
      σ.ρ h (φ w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro h w
    obtain ⟨p, hp, k0, hk0, rfl⟩ :=
      GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL k n (monotone_twoBlocks (N := n) a) h
    obtain ⟨κ, rfl⟩ := exists_inc_eq i hi k0 hk0
    rw [map_mul, Module.End.mul_apply]
    refine twKer_le_comap σ.ρ _ p (blockUpper_le_normalizer (GlobalTheory.FiniteGL.twoBlocks n a) hp) ?_
    have h1 := hφ κ w
    rw [show (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ w) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) (φ w) from rfl] at h1
    rw [← h1]
    exact hφT _
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  let S : Subrepresentation σ.ρ :=
    ⟨Submodule.span ℂ {v | ∃ (h : GL (Fin n) k) (w : τ), v = σ.ρ h (φ w)}, fun x v hv => by
      refine (Submodule.span_le.2 ?_ : _ ≤ (Submodule.span ℂ _).comap (σ.ρ x)) hv
      rintro _ ⟨h, w, rfl⟩
      exact Submodule.subset_span ⟨x * h, w, by rw [map_mul, Module.End.mul_apply]⟩⟩
  have hST : S.toSubmodule ≤ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨h, w, rfl⟩; exact hall h w)
  have hirr := σ.irr
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hm : φ w0 ∈ S.toSubmodule := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
    rw [hS] at hm
    exact hw0 ((Submodule.mem_bot ℂ).1 hm)
  · refine eq_top_iff.2 fun v _ => hST ?_
    rw [hS]
    trivial

theorem isCuspidal_of_inflates (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (τ : FDRep ℂ (Gn g n))
    (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    IsCuspidal σ.ρ := by
  refine ⟨σ.smooth, fun s d e he => ?_⟩
  obtain ⟨Q, a, h0, ha, hQ⟩ := exists_perm_conj e he
  have htop := twKer_twoBlocks_eq_top i hi h0 ha τ hτ σ hs
  have hinvQ : ∀ z, σ.ρ Q⁻¹ (σ.ρ Q z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 ≤
      (twKer σ.ρ (unipRad k e) 1).comap (σ.ρ Q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, y, rfl⟩
    refine Submodule.subset_span ⟨⟨Q * x * Q⁻¹, hQ x hx⟩, σ.ρ Q y, ?_⟩
    simp [map_mul, Module.End.mul_apply, hinvQ]
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have hv : σ.ρ Q⁻¹ v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    rw [htop]
    exact Submodule.mem_top
  have := hmap hv
  rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at this

end DiscreteGroups.sglob.DzLc

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lCusp : LCusp := by
  intro E _ _ w g _ i hi n hn τ hτ σ hs
  exact GlobalTheory.LocGL.IrrGL.isCusp_of.2 ⟨hn, DiscreteGroups.sglob.DzLc.isCuspidal_of_inflates i hi τ hτ σ hs⟩

end DiscreteGroups.sglob.DzType
