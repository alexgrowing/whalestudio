import Development.EtaleCohomology.EtaleSheaves.SHSectionPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

noncomputable section
open CategoryTheory Limits IsLocalRing

namespace LateralTheory.E.SHAlgSecPf

theorem retract_alg {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [Algebra.Etale A R] (Q : Ideal R) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A R)).IsMaximal) : Nonempty (R →ₐ[A] A) := by
  have hQm : Q.comap (algebraMap A R) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hQ
  have hEt : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := R)).mpr inferInstance
    have : (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus A R := by rw [h]; trivial
    exact this
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let Rg := Localization.Away g
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (Q : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgQ
  let Q' : Ideal Rg := Q.map (algebraMap R Rg)
  have hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap R Rg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have hcomap : Q'.comap (algebraMap A Rg) = RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [IsScalarTower.algebraMap_eq A R Rg, ← Ideal.comap_comap, hQ'c, hQm,
      ResidueField.algebraMap_eq, ker_residue]
  obtain ⟨φ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := A) (K := ResidueField A) Q' hcomap
  obtain ⟨ψ, -⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale (R := A) (A := Rg) (B := A)
    (C := ResidueField A) (maximalIdeal A) (Algebra.ofId A (ResidueField A))
    (residue_surjective) (fun b => by
      simp [Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff]) φ
  exact ⟨ψ.comp (IsScalarTower.toAlgHom A R Rg)⟩

theorem SHAlgSec_of : LateralTheory.E.SHSectionPf.SHAlgSec := by
  intro A R f hA hf hQ
  obtain ⟨hH, hS⟩ := hA
  let := f.hom.toAlgebra
  have : Algebra.Etale A R := (RingHom.etale_algebraMap).mp hf
  obtain ⟨Q, hQp, hQm⟩ := hQ
  obtain ⟨σ⟩ := retract_alg (A := A) (R := R) Q hQm
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  ext a
  exact σ.commutes a

end LateralTheory.E.SHAlgSecPf
