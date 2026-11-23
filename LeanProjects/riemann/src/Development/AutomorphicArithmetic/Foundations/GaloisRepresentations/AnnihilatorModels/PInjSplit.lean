import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private def baseChangePts {R A S K : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing K]
    [Algebra R A] [Algebra R S] [Algebra A K] [Algebra R K] [IsScalarTower R A K] :
    (A ⊗[R] S →ₐ[A] K) ≃ (S →ₐ[R] K) where
  toFun f := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun g := Algebra.TensorProduct.lift (Algebra.ofId A K) g fun _ _ => Commute.all _ _
  left_inv f := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext s
      simp [Algebra.ofId_apply]
  right_inv g := by
    ext s
    simp [Algebra.ofId_apply]

theorem UpperTheory.Gal.crystallineComparison.injSplit_of :
    RankOfDeg → SplitsOfEquiv → InjSplit := by
  intro hRank hSplitEq l d R S _ _ _ hE
  haveI := hE.fin
  haveI := hE.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (Localization.Away (l : R)) K],
      Nat.card (Localization.Away (l : R) ⊗[R] S →ₐ[Localization.Away (l : R)] K) = d := by
    intro K _ _ _
    letI : Algebra R K := ((algebraMap (Localization.Away (l : R)) K).comp
      (algebraMap R (Localization.Away (l : R)))).toAlgebra
    haveI : IsScalarTower R (Localization.Away (l : R)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hl : (l : K) ≠ 0 := by
      have hu : IsUnit (algebraMap R (Localization.Away (l : R)) (l : R)) :=
        IsLocalization.Away.algebraMap_isUnit (l : R)
      have hu' := hu.map (algebraMap (Localization.Away (l : R)) K)
      simpa using hu'.ne_zero
    rw [Nat.card_congr baseChangePts]
    exact hE.deg K hl
  have hn := hRank (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) d hdeg
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨n, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨z, hz⟩ := hSplitEq (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) T (Fin n) e
  exact ⟨T, inferInstance, inferInstance, n, z,
    FaithfulSMul.algebraMap_injective (Localization.Away (l : R)) T, hz⟩
