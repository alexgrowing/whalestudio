import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
theorem tame_any_at_of_is_conj_pl_tame_gen : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  intro D hW hχ hG hF i π ρ hc ha hfull hρ k hl v w hvw hgen
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hP := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := fun h => hP (mem_placesOver_conj (isConjPl_symm hvw) h)
  have hγ0 : TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.gam0 i (D.naut.plGw k v)) := by
    refine D.nd.restN_tameGenerator_generates i _ (Or.inl ((D.nd.S_def i _).2 ⟨?_, hP⟩))
    have hv := D.naut.plGw_over k v
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hγw : TameGenAt (D.nd.plOm.1 w) (D.nd.gam0 i w) := ⟨D.nd.locNd_chebotarevPlace_mem i w, hgen⟩
  obtain ⟨g, hg⟩ := exists_tameGenAt_conj D hvw hγw
  have hkill : ∀ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ((redF D i ρ).prod (chiBar D i)) s = 1 := by
    intro u hu
    have huI := mem_ine_of_wild hu
    obtain ⟨ι, -, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
    have hf := _root_.UpperTheory.GalS.fl0' hfull k v
    unfold labSig at hf
    rw [isoLoc_single] at hf
    have h1 := (_root_.GlobalTheory.IneAway.ineAt' D hG hF i π ρ hc ha hfull hρ k v _ rfl hP u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hgv _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    refine Prod.ext h3 ?_
    change Units.map _ (D.nd.chi i 1 u) = 1
    rw [hχ i k v hl u hu, map_one]
  have hopen : IsOpen ((((redF D i ρ).prod (chiBar D i)).ker : Subgroup _) : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    exact (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1).inter (isOpen_ker_chiBar D i)
  obtain ⟨n, hn, hM, hpow⟩ := GlobalTheory.T.tameGenerator_image_eq_coprime_pow _ _ _ _ _ hγ0 hg _ _ hopen hkill
  set γ0 := D.nd.gam0 i (D.naut.plGw k v) with hγ0def
  set M := orderOf (((redF D i ρ).prod (chiBar D i)) γ0) with hMdef
  have hone : ((redF D i ρ).prod (chiBar D i)) γ0 ^ M = 1 := pow_orderOf_eq_one _
  have hinv : ((redF D i ρ).prod (chiBar D i)) (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ =
      ((redF D i ρ).prod (chiBar D i)) γ0 ^ (n * (M - 1)) := by
    rw [map_inv, hpow, inv_eq_iff_mul_eq_one, ← pow_add, ← mul_one_add, show 1 + (M - 1) = M by omega, mul_comm, pow_mul,
      hone, one_pow]
  have hn' : (n * (M - 1)).Coprime M := hn.mul_left ((Nat.coprime_self_sub_left hM).2 (Nat.coprime_one_left _))
  obtain ⟨θ, hθ, hθo, hθn⟩ := GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField (D.host.g k) M _ hM hn'
  obtain ⟨hcp, hcχ⟩ := GlobalTheory.T.inertia_compatible_conjugation_representation D hF i π ρ hc hρ w _ hw (D.nd.plOm.2 w) _ (Subgroup.inv_mem _ hγw.1)
    (cConj D.ntw (D.nd.gam0 i w)⁻¹) (fun y => by rw [cConj_apply, RingEquiv.symm_apply_apply])
  rw [inv_inv] at hcp hcχ
  have econj : (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ = g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹ := by
    rw [map_inv]
    group
  rw [econj] at hinv
  have hρ1 : redF D i ρ (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = redF D i ρ γ0 ^ (n * (M - 1)) :=
    congrArg Prod.fst hinv
  have hχ1 : chiBar D i (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = chiBar D i γ0 ^ (n * (M - 1)) :=
    congrArg Prod.snd hinv
  have hρM : redF D i ρ γ0 ^ M = 1 := congrArg Prod.fst hone
  have hχM : chiBar D i γ0 ^ M = 1 := congrArg Prod.snd hone
  obtain ⟨v', j, ι, e₁, e₂, he₁, he₂, hι, hch, hχ0⟩ := _root_.GlobalTheory.T.tame_any_at_pl_gw D hG hF i π ρ hc ha hfull hρ k hl v
  refine ⟨v', j, ι.comp θ, e₁, e₂, he₁, he₂, injPrimeTo_comp hι hθ hθo, ?_, ?_⟩
  · have h1 := charpoly_pow_of_prod _ _ _ hch (n * (M - 1))
    rw [← Units.val_pow_eq_pow_val, ← hρ1, map_mul, map_mul, map_inv _ g, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj, charpoly_redF, hcp, ← charpoly_redF] at h1
    rw [h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₁ x
      (pow_eq_one_of_prod _ _ _ hch (by rw [← Units.val_pow_eq_pow_val, hρM, Units.val_one]) hx)]
  · rw [← chiBar_val] at hχ0
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₂ _
      (by rw [← hχ0, ← Units.val_pow_eq_pow_val, hχM, Units.val_one]), ← hχ0, ← Units.val_pow_eq_pow_val, ← hχ1,
      map_mul, map_mul, map_inv _ g, mul_inv_cancel_comm, chiBar_val, chi1, chi1, hcχ]
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
