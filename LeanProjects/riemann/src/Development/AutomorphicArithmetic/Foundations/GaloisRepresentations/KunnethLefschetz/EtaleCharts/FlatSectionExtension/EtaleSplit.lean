import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι), (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).Etale := by
  intro K _ W Z Y q i π D d B α
  let E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K ≃ₐ[K] MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) :=
    (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin (B.c α).n) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv K (Fin d) (Fin (B.c α).n))
  have h : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).comp
        (E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K →+* MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K)) =
      MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, MvPolynomial.sumAlgEquiv_C_inl]
    · rintro (m | m) <;> simp [E, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have h' : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)) =
      (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t)).comp
        (E.symm : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* MvPolynomial (Fin (B.c α).n ⊕ Fin d) K) := by
    rw [← h]
    ext x
    all_goals simp
  rw [h']
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective E.symm.bijective) (B.c α).etale
