import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfPowEqSelf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_algebraMap (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dif_pos haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dif_pos hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
