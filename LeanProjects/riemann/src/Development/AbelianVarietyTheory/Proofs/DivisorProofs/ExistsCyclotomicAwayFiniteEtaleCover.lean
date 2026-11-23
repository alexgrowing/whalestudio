import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.CycAwayCover

theorem isUnit_natCast_cycAway {M : ℕ} (hM : M ≠ 0) : IsUnit (M : cycAway M) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨(M : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩, ?_⟩
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))

def awayToCyc (M : ℕ) (hM : M ≠ 0) : Localization.Away (M : ℤ) →+* cycAway M :=
  IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) (g := Int.castRingHom (cycAway M))
    (by simpa using isUnit_natCast_cycAway hM)

theorem awayToCyc_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (awayToCyc M hM) := by
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  rw [awayToCyc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away (M : ℤ)) hle).eq_iff,
    (Int.castRingHom (cycAway M)).injective_int.eq_iff]

theorem finite_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Finite := by
  letI := (awayToCyc M hM).toAlgebra
  have hv : ∀ hx, (⟨(M : ℂ)⁻¹, hx⟩ : cycAway M) =
      algebraMap (Localization.Away (M : ℤ)) (cycAway M) (IsLocalization.Away.invSelf (M : ℤ)) := by
    intro hx
    have h1 : (M : cycAway M) * ⟨(M : ℂ)⁻¹, hx⟩ = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))
    have h2 : (M : cycAway M) * algebraMap (Localization.Away (M : ℤ)) (cycAway M)
        (IsLocalization.Away.invSelf (M : ℤ)) = 1 := by
      have := congrArg (algebraMap (Localization.Away (M : ℤ)) (cycAway M))
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (M : ℤ)) (M : ℤ))
      simpa using this
    exact (isUnit_natCast_cycAway hM).mul_left_cancel (h1.trans h2.symm)
  have hint : Algebra.IsIntegral (Localization.Away (M : ℤ)) (cycAway M) := by
    constructor
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hM, by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
          exact sub_eq_zero.2 (GlobalTheory.SiegelTor.zetaAway_pow_self hM)⟩
      · convert (isIntegral_algebraMap (R := Localization.Away (M : ℤ)) (x := IsLocalization.Away.invSelf (M : ℤ)) : IsIntegral _ (algebraMap (Localization.Away (M : ℤ)) (cycAway M) _)) using 1
        exact hv _
    | zero => exact isIntegral_zero
    | one => exact isIntegral_one
    | add x y _ _ hx hy => exact hx.add hy
    | neg x _ hx => exact hx.neg
    | mul x y _ _ hx hy => exact hx.mul hy
  haveI : Algebra.FiniteType (Localization.Away (M : ℤ)) (cycAway M) := by
    refine ⟨⟨{zetaAway M}, eq_top_iff.2 ?_⟩⟩
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      · convert Subalgebra.algebraMap_mem (Algebra.adjoin (Localization.Away (M : ℤ)) ((({zetaAway M} : Finset (cycAway M)) : Set (cycAway M)))) (IsLocalization.Away.invSelf (M : ℤ)) using 1
        exact hv _
    | zero => exact Subalgebra.zero_mem _
    | one => exact Subalgebra.one_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | neg x _ hx => exact Subalgebra.neg_mem _ hx
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  exact (Algebra.IsIntegral.finite : Module.Finite (Localization.Away (M : ℤ)) (cycAway M))

theorem etale_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Etale := by
  letI := (awayToCyc M hM).toAlgebra
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  haveI : IsDomain (Localization.Away (M : ℤ)) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (M : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hle (Localization.Away (M : ℤ))
  haveI : Module.Finite (Localization.Away (M : ℤ)) (cycAway M) := finite_awayToCyc hM
  haveI : FaithfulSMul (Localization.Away (M : ℤ)) (cycAway M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (awayToCyc_injective hM)
  haveI : Module.Flat (Localization.Away (M : ℤ)) (cycAway M) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (M : ℤ)) (cycAway M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI := formallyUnramified_cycAway hM (Localization.Away (M : ℤ))
  exact (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale (Localization.Away (M : ℤ)) (cycAway M))

theorem exists_cycAway_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  intro M S hM hS
  have hM0 : M ≠ 0 := hM.ne'
  have hSu : IsUnit ((Int.castRingHom Γ(S, ⊤)) (M : ℤ)) := by simpa using hS
  let φ : S ⟶ Sp (Localization.Away (M : ℤ)) :=
    S.toSpecΓ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) hSu)
  let S' : Over S := Over.mk (pullback.fst φ (spMap (awayToCyc M hM0)))
  haveI : IsFinite (spMap (awayToCyc M hM0)) := (IsFinite.SpecMap_iff _).2 (finite_awayToCyc hM0)
  haveI : Etale (spMap (awayToCyc M hM0)) := HasRingHomProperty.Spec_iff.2 (etale_awayToCyc hM0)
  refine ⟨S', pullback.snd φ (spMap (awayToCyc M hM0)), ?_, ?_, ?_⟩
  · exact (inferInstance : IsFinite (pullback.fst φ (spMap (awayToCyc M hM0))))
  · exact (inferInstance : Etale (pullback.fst φ (spMap (awayToCyc M hM0))))
  · intro T f t₁
    haveI : IsOpenImmersion (spMap (algebraMap ℤ (Localization.Away (M : ℤ)))) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (M : ℤ))))))
    have e : f ≫ φ = t₁ ≫ spMap (awayToCyc M hM0) :=
      (cancel_mono (spMap (algebraMap ℤ (Localization.Away (M : ℤ))))).1 (specZIsTerminal.hom_ext _ _)
    refine ⟨pullback.lift f t₁ e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro g ⟨h1, h2⟩
    exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ e).symm) (h2.trans (pullback.lift_snd _ _ e).symm)

end GlobalTheory.CycAwayCover
