import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTransStatement

open IsLocalRing

namespace GlobalTheory

theorem exists_strictHenselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ hΩ
  obtain ⟨H, _, _, _, _, hflat, hmax, hbij, hind⟩ := GlobalTheory.T.exists_etale_localization_filtration_henselization R
  let e : ResidueField R ≃+* ResidueField H := RingEquiv.ofBijective _ hbij
  letI algH : Algebra (ResidueField H) Ω :=
    ((algebraMap (ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (ResidueField H) Ω).comp e.toRingHom =
      (RingEquiv.refl Ω : Ω →+* Ω).comp (algebraMap (ResidueField R) Ω) := by
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  haveI : IsSepClosure (ResidueField H) Ω :=
    ⟨hΩ.sep_closed, Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ω) he⟩
  obtain ⟨T, _, _, _, _, hsc, hflat2, hmax2, ⟨e2⟩, hind2⟩ := GlobalTheory.T.exists_etale_localization_filtration_strictHenselization H Ω
  letI algRT : Algebra R T := ((algebraMap H T).comp (algebraMap R H)).toAlgebra
  haveI : IsScalarTower R H T := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalHom (algebraMap R T) := by
    change IsLocalHom ((algebraMap H T).comp (algebraMap R H))
    infer_instance
  refine ⟨T, inferInstance, algRT, inferInstance, hloc, hsc, ?_, ?_, ?_, ?_⟩
  · haveI := hflat; haveI := hflat2
    exact Module.Flat.trans R H T
  · rw [IsScalarTower.algebraMap_eq R H T, ← Ideal.map_map, hmax, hmax2]
  · refine ⟨{ e2 with commutes' := ?_ }⟩
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    have h1 : algebraMap (ResidueField R) (ResidueField T) (residue R x) =
        algebraMap (ResidueField H) (ResidueField T) (residue H (algebraMap R H x)) := by
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue]; rfl
    have h2 : algebraMap (ResidueField H) Ω (residue H (algebraMap R H x)) =
        algebraMap (ResidueField R) Ω (residue R x) := by
      rw [RingHom.algebraMap_toAlgebra]
      simp only [RingHom.comp_apply]
      congr 1
      apply e.symm_apply_eq.mpr
      rfl
    show e2 (algebraMap (ResidueField R) (ResidueField T) (residue R x)) = _
    rw [h1, AlgEquiv.commutes, h2]
  · exact GlobalTheory.T.indEtale_localizedPieces_trans R H T hind hind2

end GlobalTheory
