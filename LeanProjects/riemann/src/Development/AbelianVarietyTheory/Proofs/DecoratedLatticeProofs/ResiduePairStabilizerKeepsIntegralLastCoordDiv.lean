import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.PairKeep

theorem res_zero_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c τ : k) (q : Unif k) (hτ : valuation k τ = valuation k ((q.1 : 𝒪[k]) : k)) (hc : valuation k c = 1)
    (x : k) (s : 𝒪[k]) (hs : (s : k) = c * x) :
    IsLocalRing.residue 𝒪[k] s = 0 ↔ ∃ t ∈ 𝒪[k], x = τ * t := by
  have hq := q.ne_zero
  have hvq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using hq
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, map_zero] at hτ; exact hvq hτ.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  rw [IsLocalRing.residue_eq_zero_iff, q.mem_max_iff]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : ((q.1 : 𝒪[k]) : k) / (c * τ) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨_, mul_mem h1 t.2, ?_⟩
    have h2 : c * x = ((q.1 : 𝒪[k]) : k) * (t : k) := by rw [← hs, ht]; rfl
    field_simp
    linear_combination h2
  · rintro ⟨t, ht, rfl⟩
    have h1 : (c * τ) / ((q.1 : 𝒪[k]) : k) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨⟨_, mul_mem h1 ht⟩, Subtype.ext ?_⟩
    rw [hs]
    change _ = ((q.1 : 𝒪[k]) : k) * (c * τ / ((q.1 : 𝒪[k]) : k) * t)
    field_simp

theorem keep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  intro k _ _ _ _ m' m hm b b' hbb hb'b P hP c τ q hτ hc hval g hg
  subst hm
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hmul : ∀ g₁ g₂ : GL (Fin m') k, g₁ * g₂ = 1 → (b * g₁.val * b') * (b * g₂.val * b') = 1 := by
    intro g₁ g₂ h
    have h' : g₁.val * g₂.val = 1 := by rw [← Units.val_mul, h, Units.val_one]
    calc (b * g₁.val * b') * (b * g₂.val * b') = b * (g₁.val * (b' * b) * g₂.val) * b' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb'b, Matrix.mul_one, h', Matrix.mul_one, hbb]
  have hb' : ∀ (g : GL (Fin m') k) (u : Fin m' → k), b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u) := by
    intro g u
    change _ = g.val *ᵥ (b' *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]
  have hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    rw [hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  have hint : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu
    rw [← hlat, hb']
    have := ((P.hasVal_fn ⟨_, (hlat u).2 hu⟩).gl_smul g)
    rw [hg] at this
    exact this.mem
  have hlast : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k,
      ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], u r0 = τ * s) →
      ((∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k]) ∧
        ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], ((b * g.val * b') *ᵥ u) r0 = τ * s) := by
    intro g hg u ⟨hu, hu'⟩
    refine ⟨hint g hg u hu, fun r0 hr0 => ?_⟩
    obtain ⟨s, hs, hv⟩ := hval u hu r0 hr0
    obtain ⟨s', hs', hv'⟩ := hval _ (hint g hg u hu) r0 hr0
    have h1 := hv.gl_smul g
    rw [hg, ← hb'] at h1
    rw [← res_zero_iff c τ q hτ hc _ s' hs', hv'.unique h1, res_zero_iff c τ q hτ hc _ s hs]
    exact hu' r0 hr0
  have htr : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b')ᵀ *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu r
    have h1 := hint g hg (Pi.single r 1) (fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    rw [Matrix.mulVec_single_one] at h1
    change ∑ j, (b * g.val * b')ᵀ r j * u j ∈ 𝒪[k]
    exact sum_mem fun j _ => mul_mem (h1 j) (hu j)
  have hg' : g⁻¹ • P = P := by rw [inv_smul_eq_iff, hg]
  refine ⟨hmul _ _ (mul_inv_cancel g), fun u => ⟨hlast g hg u, fun h => ?_⟩, fun u => ⟨htr _ hg' u, fun h => ?_⟩⟩
  · have := hlast _ hg' _ h
    rwa [Matrix.mulVec_mulVec, hmul _ _ (inv_mul_cancel g), Matrix.one_mulVec] at this
  · have := htr _ hg _ h
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmul _ _ (inv_mul_cancel g), Matrix.transpose_one,
      Matrix.one_mulVec] at this

end GlobalTheory.PairKeep
