import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

noncomputable section

namespace GlobalTheory.RowWildTame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem main : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.LabTame D.nd D.naut → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  intro D hT hL hR σ k v i hl hocc hgood s hs hwild
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hc⟩ := hR i σ hocc hgood
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, hιi⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have e := hc k v hl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rw [e, D.naut.lpDim_tw] at this
    exact this
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have h1 := hL k v _ hfull s hs hwild
  rw [hdim] at h1
  have h2 := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont s hs
  rw [e, D.naut.inePol_tw _ _ _ hs, h1] at h2
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have h3 : ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i)
      ((D.naut.iotaQC i).injective.comp hιi)
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, hcomp,
      ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact h2
  have h4 := hT.2 i σ hocc hgood Sig ρ hP hρ s
  rw [h3, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h4
  have h5 : ((D.ntypes.rbar σ (D.nd.w i) s : GL (Fin D.R.r) (Fb (D.what₂.places.resChar (D.nd.w i))
      (D.what₂.places.resChar_prime (D.nd.w i)))) : Matrix (Fin D.R.r) (Fin D.R.r)
      (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
      (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
      (RingHom.injective _)
    rw [h4, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  have h6 : s ∈ (D.ntypes.rbar σ (D.nd.w i)).ker := by
    refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _ inferInstance
      (D.ntypes.rbar_open σ _) s ((D.what₂.places.resChar (D.nd.w i)) ^ D.R.r) (fun hmem => hw ?_) hwild ?_
    · rw [Nat.cast_pow, D.nd.w_l i] at hmem
      exact (D.naut.plGw k v).isPrime.mem_of_pow_mem _ hmem
    · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
      exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ h5
  exact h6

end GlobalTheory.RowWildTame
