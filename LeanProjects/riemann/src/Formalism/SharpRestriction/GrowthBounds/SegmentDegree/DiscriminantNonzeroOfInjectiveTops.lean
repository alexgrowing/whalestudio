import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CoarseLabelFactorisation
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrobeniusReductionProduct

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateVectorsDistinctLeadingTerms : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective fun a : Fin r => posOf n' (X.row j x a)

open Classical in

theorem ph_detPl_ne_zero {R : Type} [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)
    (hp : 0 < p) (j x : ℤ) (hinj : Function.Injective fun a : Fin r => posOf n' (X.row j x a)) :
    phSeg R K p X.F j (plEmb R r K (X.detPl R j x)) ≠ 0 := by
  intro h
  let v : Fin n' × Fin (r + K) → R := fun tc =>
    if ∃ a : Fin r, posOf n' (X.row j x a) = tc.1 ∧ tc.2 = Fin.castAdd K a then 1 else 0
  let f : MvPolynomial (ℤ × Fin r) R →+* R :=
    (MvPolynomial.eval v).comp ((phSeg R K p X.F j).toRingHom.comp (plEmb R r K).toRingHom)
  have h1 : f (X.detPl R j x) = 0 := by
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) = 0
    rw [h, map_zero]
  have hm : f.mapMatrix (Matrix.of fun a b : Fin r => MvPolynomial.X (X.row j x a, b)) = 1 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x a, b)))) = (1 : Matrix (Fin r) (Fin r) R) a b
    simp only [plEmb, rename_X, phSeg, aeval_X, map_pow, eval_X]
    by_cases hab : a = b
    · subst hab
      have hv : v (posOf n' (X.row j x a), Fin.castAdd K a) = 1 := if_pos ⟨a, rfl, rfl⟩
      rw [hv, one_pow, Matrix.one_apply_eq]
    · have hv : v (posOf n' (X.row j x a), Fin.castAdd K b) = 0 := by
        apply if_neg
        rintro ⟨a', ha, hb⟩
        have e1 : a' = a := hinj ha
        have e2 : b = a' := Fin.castAdd_injective _ _ hb
        exact hab (e2.trans e1).symm
      rw [hv, zero_pow (pow_ne_zero _ hp.ne'), Matrix.one_apply_ne hab]
  have h2 : f (X.detPl R j x) = 1 := by
    unfold Dat.detPl
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h1] at h2
  exact zero_ne_one h2

theorem discriminant_nonzero_of_injective_tops (hInj : LateVectorsDistinctLeadingTerms) : DiscriminantNonzeroModUniformiser := by
  intro p n' r K _ _ _ X O _ _ _ hX
  have hp : 0 < p := hX.prime.pos
  have hpl : ∀ P : MvPolynomial (ℤ × Fin r) O,
      map (IsLocalRing.residue O) (plEmb O r K P) = plEmb _ r K (map (IsLocalRing.residue O) P) := by
    intro P
    simp [plEmb, MvPolynomial.map_rename]
  simp only [Dat.Dl, Dat.DlSeg, map_prod, map_pow, map_phSeg, hpl, map_detPl]
  rw [Finset.prod_ne_zero_iff]
  intro j _
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  exact pow_ne_zero _ (ph_detPl_ne_zero X p K hp _ _ (hInj p n' r K X hX _ x hx))

end Formalism.MainNotions.SelectionLemmas.Pf
