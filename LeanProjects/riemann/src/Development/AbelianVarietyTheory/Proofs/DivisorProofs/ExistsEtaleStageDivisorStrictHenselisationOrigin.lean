import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem exists_stage_divisor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq b c s hs hbc
  classical
  let I : Ideal (MvPolynomial (Fin 2) (Polynomial T)) :=
    Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)}
  haveI : Algebra.FinitePresentation (Polynomial T) (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))
  have hI : ∀ a ∈ I, MvPolynomial.aeval (R := Polynomial T) ![b, c] a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (MvPolynomial.aeval (R := Polynomial T) ![b, c]) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      show b * c - _ = 0
      rw [hbc, IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq, sub_self]
    exact hle ha
  let g : (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) →ₐ[Polynomial T] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![b, c]) hI
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime
    (Polynomial T) O P φ hφ hSH.2.2.2 _ g
  letI : Algebra T W := ((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI : IsScalarTower T (Polynomial T) W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set Q : Ideal W := (maximalIdeal O).comap v.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) W) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : v.toRingHom.comp (algebraMap (Polynomial T) W) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact v.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.comap_maximalIdeal (R := Polynomial T) (I := P)
  have hunit : ∀ y : Q.primeCompl, IsUnit (v.toRingHom (y : W)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : W) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap W (Localization.AtPrime Q)) = v.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) W (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact v.comp_algebraMap
  have hjW : ∀ w : W, j (algebraMap W (Localization.AtPrime Q) w) = v w := fun w =>
    congrArg (fun f => f w) hjE
  have hgX : ∀ i : Fin 2, v (u (Ideal.Quotient.mk I (MvPolynomial.X i))) = ![b, c] i := by
    intro i
    rw [← AlgHom.comp_apply, huv]
    show Ideal.Quotient.liftₐ I _ hI (Ideal.Quotient.mk I _) = _
    change MvPolynomial.aeval ![b, c] (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hprod : Ideal.Quotient.mk I (MvPolynomial.X 0) * Ideal.Quotient.mk I (MvPolynomial.X 1) =
      algebraMap (Polynomial T) _ (Polynomial.C s) := by
    rw [← map_mul, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 0))),
    algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 1))), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod, AlgHom.commutes,
      IsScalarTower.algebraMap_apply T W (Localization.AtPrime Q)]
    rfl
  · rw [hjW, hgX]; rfl
  · rw [hjW, hgX]; rfl

end GlobalTheory.KeyOriginCut
