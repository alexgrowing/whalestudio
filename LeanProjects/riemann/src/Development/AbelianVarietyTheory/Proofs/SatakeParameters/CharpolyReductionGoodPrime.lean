import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapEqProdOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar

noncomputable section

namespace GlobalTheory.ResidualTame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem charpoly_tameGen : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  intro D hT hI hR σ k v i hl hocc hgood
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hW⟩ := hR i σ hocc hgood
  obtain ⟨B, κ, h1, h2⟩ := hI i
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (k := k) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rwa [hW k v hl, D.naut.lpDim_tw] at h
  have hfull : (D.naut.items₂ k _ (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hine : ((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (iotaO D.nd D.naut i) =
      ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    have e := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont _ (D.ntypes.tg_mem k v)
    rw [hW k v hl, D.naut.inePol_tw _ _ _ (D.ntypes.tg_mem k v), D.ntypes.inertiaCharpoly_type k v _ hfull,
      ← D.naut.lab_loc i k σ v] at e
    rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact e
  have hred := GlobalTheory.TypeLeaf.map_eq_prod_of_valuationSubring B (iotaO D.nd D.naut i)
    (((fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom.comp
      κ.toRingHom).comp (IsLocalRing.residue B))
    ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) h1 (D.ntypes.teichC k)
    (fun x => fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
      (D.ntypes.iota k v (D.nd.w i) x))
    (fun x => by
      obtain ⟨h, e⟩ := h2 k v x
      exact ⟨h, congrArg (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out) e⟩)
    _ _ hine
  rw [← hT.2 i σ hocc hgood Sig ρ hP hρ (D.ntypes.tg k v)] at hred
  apply Polynomial.map_injective
    (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
    (RingHom.injective _)
  rw [hred, Polynomial.map_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  simp [GlobalTheory.TypeLeaf.map_primeToPart_fbar]

end GlobalTheory.ResidualTame
