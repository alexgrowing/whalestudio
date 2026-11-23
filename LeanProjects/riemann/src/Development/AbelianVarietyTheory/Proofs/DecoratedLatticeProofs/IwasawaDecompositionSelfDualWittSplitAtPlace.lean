import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWittStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

variable {D : D7}

theorem flag_times_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ p ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S p ⬝ d.jX = d.jX ⬝ a) ∧ Moves S (p⁻¹ * h) L L (· = v) := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨q, hq, ⟨a, ha, hqa⟩, Λ₀, hΛ, hz⟩ := GlobalTheory.T.exists_flag_stabiliser_move_lattice_split_witt D S S₀ ρ d L L₀ v hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D S L v hL) hM h hh
  obtain ⟨γ, hγ, hγL⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D S₀ v _ Λ₀ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D S₀ L₀ v hL₀) hΛ
  refine ⟨q * d.emb0 γ, mul_mem hq (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ), ⟨a, ha, ?_⟩, ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hqa]
  · intro y hy
    obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((q * d.emb0 γ)⁻¹ * h) *ᵥ y := ⟨_, rfl⟩
    rw [← hzdef]
    have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
    have hw : y = mt S (h⁻¹ * q) *ᵥ (mt S (d.emb0 γ) *ᵥ z) := by
      rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
      have : h⁻¹ * q * d.emb0 γ * ((q * d.emb0 γ)⁻¹ * h) = 1 := by group
      rw [this, mt_one, Matrix.one_mulVec]
    have key := hz (mt S (d.emb0 γ) *ᵥ z) (mulVec_mem_idAt _ hzI)
    rw [← hw] at key
    rw [key, hM z, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding,
      ← Matrix.mulVec_mulVec, ← hγL _ (mulVec_mem_idAt _ hzI)]

theorem iwasawa_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), ∃ κ, InK S L (· = v) κ ∧ h = n * d.levi t * d.emb0 γ * κ := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨p, hp, hflag, hmv⟩ := flag_times_stab D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨n, hn, hnv, t, ht, htv, γ, hγ, hpe⟩ := GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace D S S₀ ρ d v p hp hflag
  refine ⟨n, hn, hnv, t, ht, htv, γ, hγ, p⁻¹ * h, ⟨mul_mem (inv_mem hp) hh, hmv⟩, ?_⟩
  rw [← hpe]; group

end GlobalTheory.IwaPlace

end
