import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIsDomainIsIntegrallyClosed
open IsLocalRing

namespace GlobalTheory

namespace LocIndEtale

open Polynomial

lemma isIntegrallyClosed_of_forall_monic_root (T : Type) [CommRing T] [IsDomain T]
    (h : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  rintro x ⟨p, hpm, hp⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : p = 1 := hpm.natDegree_eq_zero.mp hn
      subst this
      simp at hp
    · obtain ⟨r, hr⟩ := h p hpm (hn ▸ hpos)
      have hroot : IsRoot p r := hr
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
      set q := p /ₘ (X - C r) with hq
      have hqm : q.Monic := by
        refine Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) ?_
        rw [hfac]; exact hpm
      have hqdeg : q.natDegree < n := by
        rw [hq, Polynomial.natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
        omega
      rw [← hfac, eval₂_mul] at hp
      rcases mul_eq_zero.mp hp with h1 | h1
      · refine ⟨r, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.mp h1).symm
      · exact ih _ hqdeg q hqm h1 rfl

end LocIndEtale

theorem locIndEtale_isDomain_isIntegrallyClosed :
    ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ∧ IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := by
  intro T O _ _ _ _ _ _ _ _ _ n hT _ _ hind
  haveI : IsIntegrallyClosed T := LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hT.2
  obtain ⟨hdom, hic⟩ := indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind

  have hinj : Function.Injective (algebraMap T O) := by
    obtain ⟨ι, _, _, _, Si, -, -, hloc⟩ := hind
    obtain ⟨A, _, _, _, P, _, ⟨e⟩⟩ := hloc (Classical.arbitrary ι)
    haveI : Module.Flat (Polynomial T) (Localization.AtPrime P) := inferInstance
    have hL : Function.Injective (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
      rw [injective_iff_map_eq_zero]
      intro f hf
      by_contra hne
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := Localization.AtPrime P) (mem_nonZeroDivisors_of_ne_zero hne)
      have h1 : f • (1 : Localization.AtPrime P) = f • 0 := by
        rw [Algebra.smul_def, hf, zero_mul, smul_zero]
      exact one_ne_zero (hreg h1)
    have hS : Function.Injective (algebraMap (Polynomial T) O) := by
      have : (algebraMap (Polynomial T) O) =
          (Si (Classical.arbitrary ι)).val.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial T) (Localization.AtPrime P))) := by
        ext f
        · simp
        · simp
      rw [this]
      exact Subtype.val_injective.comp (e.injective.comp hL)
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
    exact hS.comp Polynomial.C_injective
  have hle : Algebra.algebraMapSubmonoid O (nonZeroDivisors T) ≤ nonZeroDivisors O := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ht (hinj ?_)
    rw [h, map_zero]
  exact ⟨IsLocalization.isDomain_localization hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory
