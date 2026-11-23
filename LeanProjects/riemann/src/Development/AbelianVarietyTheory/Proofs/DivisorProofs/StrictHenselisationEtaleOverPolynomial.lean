import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens {A B : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal B).comap f = maximalIdeal A := by
  ext x
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private lemma locPiecesEtale_localization_atPrime {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] :
    _root_.GlobalTheory.LocAcyc.LocPiecesEtale R (Localization.AtPrime q) := by
  unfold _root_.GlobalTheory.LocAcyc.LocPiecesEtale
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
    fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨A, inferInstance, inferInstance, inferInstance, q,
      inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.strictHenselisation_etale_over_polynomial : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S)
      (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T E _ _ _ _ _ _ _ _ y _
  obtain ⟨S, _, _, _, _, hsep, hflat, -, -, hpieces⟩ := _root_.GlobalTheory.exists_strictHenselisation
    (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))
  haveI := hsep
  have hP : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Localization.AtPrime y) S := hpieces
  letI : Algebra E S :=
    ((algebraMap (Localization.AtPrime y) S).comp (algebraMap E (Localization.AtPrime y))).toAlgebra
  letI : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  letI : Algebra (Polynomial T) S := ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  haveI : IsScalarTower E (Localization.AtPrime y) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    exact congrArg _ (IsScalarTower.algebraMap_apply T (Polynomial T) E x)
  haveI : IsScalarTower (Polynomial T) (Localization.AtPrime y) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap (Localization.AtPrime y) S (algebraMap E (Localization.AtPrime y)
          (algebraMap (Polynomial T) E x)) =
        algebraMap (Localization.AtPrime y) S (algebraMap (Polynomial T) (Localization.AtPrime y) x)
      exact congrArg _ (IsScalarTower.algebraMap_apply (Polynomial T) E (Localization.AtPrime y) x).symm
  have hcomap : (maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E (Localization.AtPrime y) S, ← Ideal.comap_comap,
      _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
    exact Localization.AtPrime.comap_maximalIdeal ..
  haveI : Module.Flat E (Localization.AtPrime y) := IsLocalization.flat _ y.primeCompl
  haveI := hflat
  have hflatE : Module.Flat E S := Module.Flat.trans E (Localization.AtPrime y) S
  have hpiecesE : _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S :=
    _root_.GlobalTheory.indEtale_localPieces_trans E (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := E) (A := E) y) hP
  have hpiecesT : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Polynomial T) S :=
    _root_.GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := Polynomial T) (A := E) y) hP
  obtain ⟨P, _, φ, hφc, hφs⟩ := _root_.GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S hpiecesT
  have hPy : P = y.comap (algebraMap (Polynomial T) E) := by
    haveI : IsLocalHom φ := hφs.2.2.1
    calc P = ((maximalIdeal S).comap φ).comap (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
          rw [_root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
          exact (Localization.AtPrime.comap_maximalIdeal ..).symm
      _ = (maximalIdeal S).comap (algebraMap (Polynomial T) S) := by
          rw [Ideal.comap_comap, hφc]
      _ = y.comap (algebraMap (Polynomial T) E) := by
          rw [IsScalarTower.algebraMap_eq (Polynomial T) E S, ← Ideal.comap_comap, hcomap]
  subst hPy
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomap, hflatE, hpiecesE, φ, hφc, hφs⟩

end GlobalTheory
