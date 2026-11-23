import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpenStatement

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

theorem tameFixed_of_cuspidal : ∀ D : D7, WildOne D → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  intro D hW hG hF i π ρ hc ha hfull hρ k hl v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  have hw := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hine := GlobalTheory.T.inertia_charpoly_eq D hG hF i π ρ hc ha hρ _ hw
  obtain ⟨ι, hι, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
  have hf := hfull k v
  unfold labSig at hf ⊢
  rw [isoLoc_single] at hf ⊢
  refine ⟨ι, hι, ?_, ?_⟩
  · have h1 := (hine _ (D.ntypes.tg_mem k v)).trans (D.ntypes.inertiaCharpoly_type k v _ hf)
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x => X - C (D.ntypes.teichC k x)).prod at h1
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x =>
      X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod
    set m := rts (k := k) (v := v) (D.naut.locG π _) with hm
    have hne : ∀ x ∈ m, x ≠ 0 := by
      rintro x hx rfl
      have h2 : (X : ℂ[X]) ∣ (m.map fun x => X - C (D.ntypes.teichC k x)).prod := by
        refine Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, hx, ?_⟩)
        rw [teich_zero _ (D.ntypes.teichC_inj k), map_zero, sub_zero]
      rw [← h1, ← Matrix.charpoly_map, X_dvd_iff] at h2
      have h3 := Matrix.det_eq_sign_charpoly_coeff
        (((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
      rw [h2, mul_zero] at h3
      exact (Matrix.GeneralLinearGroup.map (iotaO D.nd D.naut i) (ρ (D.ntypes.tg k v))).det_ne_zero h3
    rw [charpoly_redF, hred _ m h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [map_primeToPart ι (isOfFinOrder_of_ne_zero (hne x hx))]
  · obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 (D.naut.plGw k v))
    rw [normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)] at hφ
    refine ⟨φ, ?_⟩
    set t := D.ntypes.tg k v with ht
    have hu := wild_of_frob (D.ntypes.tg_mem k v) hφ
    have huI : (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (D.ntypes.tg_mem k v) _))
        (conj_mem_Ine hφ.1 (D.ntypes.tg_mem k v))
    set u := (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) with hudef
    have h1 := (hine u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hg : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hg _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    rw [hudef, map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
    exact h3.symm

end GlobalTheory.TypeLeaf
