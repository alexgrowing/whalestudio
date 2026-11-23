import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleAway

theorem isEtaleAt_of_formallyEtale_baseChange (S B : Type) [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) [Q.IsPrime]
    (h : Algebra.FormallyEtale (Localization.AtPrime (Q.under S))
      (TensorProduct S (Localization.AtPrime (Q.under S)) B)) :
    Algebra.FormallyEtale S (Localization.AtPrime Q) := by
  set P : Ideal S := Q.under S with hP
  let M : Submonoid B := Algebra.algebraMapSubmonoid B P.primeCompl
  let Bp := Localization M
  have hpush : Algebra.IsPushout S (Localization.AtPrime P) B Bp :=
    (Algebra.isPushout_of_isLocalization P.primeCompl (Localization.AtPrime P) B Bp).symm
  let e : Localization.AtPrime P ⊗[S] B ≃ₐ[Localization.AtPrime P] Bp := hpush.equiv
  have h1 : Algebra.FormallyEtale (Localization.AtPrime P) Bp := Algebra.FormallyEtale.of_equiv e
  have h0 : Algebra.FormallyEtale S (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have h2 : Algebra.FormallyEtale S Bp := Algebra.FormallyEtale.comp S (Localization.AtPrime P) Bp
  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [P, Ideal.under] using hx
  letI : Algebra Bp (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsScalarTower B Bp (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  have h3 : Algebra.FormallyEtale Bp (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl)
  haveI : IsScalarTower S Bp (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [IsScalarTower.algebraMap_apply S B Bp, ← IsScalarTower.algebraMap_apply B Bp,
      ← IsScalarTower.algebraMap_apply S B])
  exact Algebra.FormallyEtale.comp S Bp (Localization.AtPrime Q)

end GlobalTheory.EtaleAway

namespace GlobalTheory.EtaleAway

theorem formallyEtale_away : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A],
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g)
      (TensorProduct R (Localization.Away g) A) := by
  intro R _ _ _ A _ _ _ he g hg
  set S := Localization.Away g
  set B := S ⊗[R] A
  refine Algebra.etaleLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun Q => ?_)
  show Algebra.FormallyEtale S (Localization.AtPrime Q.asIdeal)
  apply isEtaleAt_of_formallyEtale_baseChange
  set P : Ideal S := Q.asIdeal.under S
  set q : Ideal R := P.under R with hq
  have hqm : q ≠ maximalIdeal R := by
    intro h
    have hgq : g ∈ q := h ▸ hg
    have : algebraMap R S g ∈ P := hgq
    exact (Ideal.IsPrime.ne_top inferInstance)
      (P.eq_top_of_isUnit_mem this (IsLocalization.Away.algebraMap_isUnit g))
  haveI := he q hqm
  haveI : P.LiesOver q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime q] (Localization.AtPrime q ⊗[R] A)
      ≃ₐ[Localization.AtPrime P] Localization.AtPrime P ⊗[S] (S ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime q) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R S (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  haveI : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[S] (S ⊗[R] A)) :=
    Algebra.Etale.of_equiv e
  infer_instance

end GlobalTheory.EtaleAway
