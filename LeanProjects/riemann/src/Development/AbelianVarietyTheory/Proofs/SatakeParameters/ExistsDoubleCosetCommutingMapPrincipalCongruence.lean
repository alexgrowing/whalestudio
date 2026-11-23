import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruence
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIsoMap

theorem isoMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  classical
  intro L _ _ _ n a S₁ S₂ hS₁ hiso N hN hex
  obtain ⟨T, hT⟩ := hiso
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (S₂.subtype ∘ₗ T.toLinearMap)
  have hφS : ∀ f (hf : f ∈ S₁), φ f = ((T ⟨f, hf⟩ : S₂) : GAf L n → a.W) := by
    intro f hf
    have := LinearMap.congr_fun hφ ⟨f, hf⟩
    simpa using this
  have hrt : ∀ h (f : GAf L n → a.W), f ∈ S₁ → φ (NG.rt L n h f) = NG.rt L n h (φ f) := by
    intro h f hf
    have hf' : NG.rt L n h f ∈ S₁ := hS₁.1.stable h f hf
    rw [hφS _ hf', hφS _ hf]
    exact hT h ⟨f, hf⟩ ⟨_, hf'⟩ rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro f hf hfix
    refine ⟨?_, fun κ hκ => ?_⟩
    · rw [hφS _ hf]; exact (T ⟨f, hf⟩).2
    · rw [← hrt κ f hf, hfix κ hκ]
  · obtain ⟨f, hf, hfix, hne⟩ := hex
    refine ⟨f, hf, hfix, ?_⟩
    rw [hφS _ hf]
    intro h0
    apply hne
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff T).1 this)
    simpa using this
  · intro g f hf hfix
    set J := GlobalTheory.IsotOrth.congSub L n N with hJ
    set D : Set (GAf L n) := {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * g * u'} with hD
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.ConjCong.exists_cong_conj L n N g hN
    have hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite := by
      refine ((GlobalTheory.HeckeRecon.finite_cosets (L := L) (n := n) (N * M) (Nat.mul_pos hN hM)).image
        (fun c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M) => ((c.out * g : GAf L n) : GAf L n ⧸ J))).subset ?_
      rintro _ ⟨x, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)), ⟨u, (show NG.Cong L n N u from hu).1, rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k ∈ GlobalTheory.IsotOrth.congSub L n (N * M),
          (Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))) = u * k := by
        have h1 := QuotientGroup.out_eq' (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))
        rw [QuotientGroup.eq] at h1
        exact ⟨_, Subgroup.inv_mem _ h1, by group⟩
      obtain ⟨hkmem, hkeq⟩ := hk
      show ((Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)) * g : GAf L n) : GAf L n ⧸ J) = ((u * g * u' : GAf L n) : GAf L n ⧸ J)
      rw [hkeq, QuotientGroup.eq]
      have hc : g⁻¹ * k * g ∈ J := hMc k hkmem
      have : (u * k * g)⁻¹ * (u * g * u') = (g⁻¹ * k * g)⁻¹ * u' := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hc) hu'
    have hsum : ∀ F : GAf L n → a.W, NG.heckeD J D F = ∑ c ∈ hfin.toFinset,
        (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose F else 0) := by
      intro F
      funext x
      rw [GlobalTheory.HeckeRecon.heckeD_eq_sum J D hfin, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · exact hrt _ f hf
    · exact map_zero φ

end GlobalTheory.HeckeIsoMap
