import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule

open Matrix Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CapelliCoef

variable {n : ℕ} {ε : Fin n → Bool}

lemma eabV_pair {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    L (EabV ε a b f g) = EabV ε a b (fun x => L (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add, map_smul, (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h1 hg).2,
    (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h2 hg).2]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma dsigC_unitM (ab : Fin n × Fin n) (v : H) :
    PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM ab) v = EabV ε ab.1 ab.2 (fun x => σ x v) 1 := by
  simp only [PI.DSInfCharCap.dsigC, PI.DSInfCharCap.unitM, PI.DSInfCharCap.thetaJ, PI.PhMeasCore.dsig,
    EabV, EcV, RdV, cpart1, cpart2, Matrix.one_mul, sub_neg_eq_add, ← sub_eq_add_neg]

def freeAct (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smoothVec ε σ) :=
  FreeAlgebra.lift ℂ fun ab => unitAct hσ ab.1 ab.2

lemma dsigCW_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (w : List (Fin n × Fin n)) (v : smoothVec ε σ) :
    PI.DSInfCharCap.dsigCW ε σ (w.map PI.DSInfCharCap.unitM) v =
      ((w.map fun ab => unitAct hσ ab.1 ab.2).prod v : smoothVec ε σ) := by
  induction w with
  | nil => rfl
  | cons ab w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_unitM, unitAct_coe]

lemma actU_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n))
    (v : smoothVec ε σ) : PI.DSInfCharCap.actU ε σ p v = (freeAct hσ p v : smoothVec ε σ) := by
  have e : freeAct hσ = (MonoidAlgebra.lift ℂ _ _ (FreeMonoid.lift fun ab => unitAct hσ ab.1 ab.2)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := Fin n × Fin n)).toAlgHom := by
    ext1
    funext ab
    simp [freeAct, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, dsigCW_eq hσ, Finsupp.sum,
    LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, FreeMonoid.lift_apply]
  rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def IsCoef (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : H →L[ℂ] Wp)
    (B : Wq →ₗ[ℂ] smoothVec ε σ) (f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g, inUJ ε g → ∀ w, f g w = P (σ g (B w))

lemma IsCoef.smooth {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) : SmoothOnGV ε f :=
  smooth_congr (PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV ε σ P
    (LinearMap.toContinuousLinearMap ((smoothVec ε σ).subtype ∘ₗ B)) fun w => (B w).2)
    fun g hg => ContinuousLinearMap.ext fun w => h g hg w

lemma IsCoef.eab (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (a b : Fin n) :
    IsCoef ε σ P (unitAct hσ a b ∘ₗ B) (EabV ε a b f) := by
  intro g hg w
  have e1 := eabV_pair (ContinuousLinearMap.apply ℂ Wp w) h.smooth a b hg
  simp only [ContinuousLinearMap.apply_apply] at e1
  rw [e1, eabV_congr (fun x hx => h x hx w) a b hg, ← eabV_pair P (B w).2 a b hg, LinearMap.comp_apply,
    unitAct_coe, rep_eabV hσ (B w).2 a b hg]

lemma IsCoef.top (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (u : ℂ) (a b : Fin n) :
    IsCoef ε σ P (freeAct hσ (Tm (PI.DSInfCharCap.Egl n) u a b) ∘ₗ B) (Top (EabV ε) u a b f) := by
  intro g hg w
  have e := h.eab hσ a b g hg w
  have e' := h g hg w
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, PI.DSInfCharCap.Egl, freeAct, Module.algebraMap_end_apply, e', e]
  · simp [Formalism.QuantumDeterminants.Top, Tm, hab, PI.DSInfCharCap.Egl, freeAct, e]

lemma IsCoef.word (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (l : List (ℂ × Fin n × Fin n)) :
    IsCoef ε σ P (freeAct hσ (l.map fun q => Tm (PI.DSInfCharCap.Egl n) q.1 q.2.1 q.2.2).prod ∘ₗ B)
      ((l.map fun q => Top (EabV ε) q.1 q.2.1 q.2.2).foldr (fun T h => T h) f) := by
  induction l with
  | nil => simpa [Module.End.one_eq_id] using h
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
    exact ih.top hσ _ _ _

theorem capelli_coef : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  intro n ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hds P Q hQ u g hg w
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := hds.2.2.1
  let B : Wq →ₗ[ℂ] smoothVec ε σ := (Q : Wq →ₗ[ℂ] Hs).codRestrict _ hQ
  have h0 : IsCoef ε σ P B (fun x => P.comp ((σ x).comp Q)) := fun _ _ _ => rfl
  have e : Q w = (B w : Hs) := rfl
  rw [e, actU_eq hσ]
  simp only [capelli, qdetOp, qminorOp, qdet, qminor, map_sum, map_mul, map_intCast, Finset.sum_apply,
    _root_.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Pi.smul_apply,
    _root_.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := h0.word hσ (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), τ k, k)) g hg w
  simp only [List.map_ofFn, Function.comp_def] at h
  simp only [id]
  rw [h]
  simp [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]

end GlobalTheory.CapelliCoef

end
