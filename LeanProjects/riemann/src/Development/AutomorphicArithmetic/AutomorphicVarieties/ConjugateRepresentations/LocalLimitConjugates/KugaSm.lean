import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem kugaSm_map {E : Type} [Field E] {a n : ℕ} (e : Fin n → Herm E a) {A A' : Type} [Ring A] [Module ℝ A]
    [Ring A'] [Module ℝ A'] (f : A →+* A') (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] A') (h : ∀ X, L' X = f (L X)) :
    cas L' e = f (cas L e) := by
  simp only [cas, map_sum, map_sub, map_mul, h]

private theorem kugaSm_A {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r : ℝ) :
    cas (shift (smA Ξ) r) e = (cas (shift (lie E a) r) e).rTensor (Fin Ξ.d → ℂ) := by
  refine kugaSm_map e (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)).toRingHom _ _ fun X => ?_
  change _ = (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)) _
  rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (r * ell E a X) (1 : Module.End ℂ (Sm E a)), map_smul, map_one,
    algebraMap_smul]
  rfl

private theorem kugaSm_B {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r c : ℝ) (h : HasCas Ξ r c e) :
    cas (shift (smB Ξ) (-r)) e = (c : ℂ) • 1 := by
  let f : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) (Sm E a)).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have h1 : cas (shift (smB Ξ) (-r)) e = f (cas (shift Ξ.dmat (-r)) e) := by
    refine kugaSm_map e f.toRingHom _ _ fun X => ?_
    change _ = f _
    rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (-r * ell E a X) (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul,
      map_one, algebraMap_smul, smB_apply]
    rfl
  rw [h1, show cas (shift Ξ.dmat (-r)) e = _ from h, map_smul, map_one]

theorem UpperTheory.V.Cj.H.kugaSm :
    UpperTheory.V.Cj.H.KugaSm := by
  intro E _ _ _ a n e he Ξ r c hc
  obtain ⟨a1, b1, hab, -, -, hinf⟩ := smAB E a Ξ
  obtain ⟨-, -, -, l4⟩ := ellFacts E a
  have hA := l4 _ _ r a1
  have hB := l4 _ _ (-r) b1
  have hsum : shift (smA Ξ) r + shift (smB Ξ) (-r) = smLie Ξ := by
    rw [shift_add_shift]
    exact LinearMap.ext fun X => add_sub_cancel (smA Ξ X) (smLie Ξ X)
  have hcom : ∀ X Y, Commute (shift (smA Ξ) r X) (shift (smB Ξ) (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hcas : cas (shift (smB Ξ) (-r)) e - cas (shift (smA Ξ) r) e = -(casA r c e).rTensor (Fin Ξ.d → ℂ) := by
    rw [kugaSm_A, kugaSm_B e Ξ r c hc, casA, LinearMap.rTensor_sub, LinearMap.rTensor_smul, neg_sub, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.rTensor_id]
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (shift (smB Ξ) (-r) - shift (smA Ξ) r) e (0 : Co Ξ (q + 1)) X = 0 := fun q X => by
    simp [del_apply]
  refine ⟨fun ω hω hd => ?_, fun q ω hω hd => ?_⟩
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaZero E a n e _ _ _ hcom ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply] at h
    rw [app_apply]
    exact neg_eq_zero.1 h.symm
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaSucc E a n e he _ _ _ hA hB hcom q ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply, add_zero] at h
    rw [app_apply, AlternatingMap.neg_apply]
    exact (neg_eq_iff_eq_neg.1 h.symm)
