import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PscoTCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TDualProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarMSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMBlockEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMDetbPEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaCoeffCommutesModeDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaMonomialCoeffDualNumberProductEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMuEqExtDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffPartialDerivMuEqSuccMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMPencil
import Mathlib

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

theorem core : ∀ {A : Type} [CommRing A] [Algebra ℂ A] {I : Type} [Fintype I] [DecidableEq I]
    (D : I → Derivation ℂ A A) (dm : Derivation ℂ A A) (J : Ideal A) (Z : Matrix I I A) (u η : I → A) (E μ r : A),
    (∀ x y, dm (Z x y) = D x (u y)) → (∀ w x y, D w (Z x y) = D x (Z w y)) → dm E = 0 →
    (∀ x, D x E + μ * D x r * E - E * ∑ y, Z x y * η y ∈ J) → r = ∑ y, η y * u y →
    dm (E * Z.det) + r * (E * Z.det) -
      ∑ x, (D x (E * ∑ y, Z.adjugate y x * u y) + μ * D x r * (E * ∑ y, Z.adjugate y x * u y)) ∈ J :=
  GlobalTheory.psco_t_core

theorem dM_comm : ∀ {n : ℕ} (ε : Fin n → Bool) (w x : Mode ε) (P : Poly n), dM ε w (dM ε x P) = dM ε x (dM ε w P) :=
  GlobalTheory.PsCo.DMComm.dM_comm

theorem coefM_dMu : ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (k : ℕ) (s : PolyM n L),
    coefM n L k (dMu L ε x s) = dL L ε x (coefM n L k s) :=
  GlobalTheory.PsCo.Cw2a.coefM_dMu

theorem coefM_pencil : ∀ {n L : ℕ} {I : Type} [Fintype I] [DecidableEq I] (A0 B0 : Matrix I I (PolyL n L)),
    let Z : Matrix I I (PolyM n L) := fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)
    (∀ k, Fintype.card I < k → coefM n L k Z.det = 0) ∧ coefM n L (Fintype.card I) Z.det = A0.det ∧
      ∀ k x y, Fintype.card I ≤ k → coefM n L k (Z.adjugate y x) = 0 :=
  GlobalTheory.coefM_pencil

end GlobalTheory.PsCo.Pc1.A

end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

variable {n L : ℕ}

section Obj

variable (ε : Fin n → Bool) (L : ℕ)

def i2 : Poly n →ₐ[ℂ] PolyM n L := (inM n L).comp (inL n L)

def Zm (A0 B0 : Matrix (Mode ε) (Mode ε) (PolyL n L)) : Matrix (Mode ε) (Mode ε) (PolyM n L) :=
  fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)

def JL : Ideal (PolyL n L) := Ideal.span (Set.range fun i : Fin L => laL n i ^ 2)

def JM : Ideal (PolyM n L) := Ideal.span (Set.range fun i : Fin L => inM n L (laL n i) ^ 2)

end Obj

section Key

variable {n L : ℕ} (ε : Fin n → Bool)

def pencilDerivativePartMatrix (L : ℕ) : Matrix (Mode ε) (Mode ε) (PolyL n L) := fun x y => inL n L (OmP ε x y)

def pencilConstantPartMatrix (c : Fin L → Mode ε → Mode ε → ℂ) : Matrix (Mode ε) (Mode ε) (PolyL n L) :=
  fun x y => ∑ i, laL n i * C (c i x y)

def dualNumberFactorsProduct (m : Fin L → Poly n) : PolyL n L := ∏ i, (1 + laL n i * inL n L (m i))

def pencilDeterminantWeight (M : ℕ) (m : Fin L → Poly n) : PolyL n L := inL n L (detbP n ^ M) * dualNumberFactorsProduct m

end Key

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pderiv_mu_lambdaPoly_lemma_5 (f : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    pderiv none (_root_.GlobalTheory.PsCo.Pc1.A.inM n L f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inM]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.inM, pderiv_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pderiv_mu_muVariable_lemma_6 : pderiv none (_root_.GlobalTheory.PsCo.Pc1.A.muM n L) = 1 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.muM, pderiv_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_lambdaPoly_lemma_7 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (f : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.inM n L f) =
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inM]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.dMu, _root_.GlobalTheory.PsCo.Pc1.A.inM, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaModeDerivation_entryPoly_lemma_8 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (P : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    _root_.GlobalTheory.PsCo.Pc1.A.dL L ε x (_root_.GlobalTheory.PsCo.Pc1.A.inL n L P) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.dM ε x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [_root_.GlobalTheory.PsCo.Pc1.A.inL]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add]
    simp [_root_.GlobalTheory.PsCo.Pc1.A.dL, _root_.GlobalTheory.PsCo.Pc1.A.inL, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_muVariable_lemma_9 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.muM n L) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.dMu, _root_.GlobalTheory.PsCo.Pc1.A.muM, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaModeDerivation_variable_lemma_10 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (i : Fin L) :
    _root_.GlobalTheory.PsCo.Pc1.A.dL L ε x (_root_.GlobalTheory.PsCo.Pc1.A.laL n i) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.dL, _root_.GlobalTheory.PsCo.Pc1.A.laL, mkDerivation_X]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma modeDerivation_offDiagonalEntry_lemma_21 (x j : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.dM ε x (X (Sum.inl j.1)) = 0 := by
  obtain ⟨⟨r, c⟩, hr, hc⟩ := j
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  simp only [_root_.GlobalTheory.PsCo.Pc1.dM, _root_.GlobalTheory.PsCo.Pc1.dZ, mkDerivation_X, Sum.elim_inl,
    Matrix.single_apply]
  have h1 : a ≠ c := fun h => by simp_all
  have h2 : b ≠ r := fun h => by simp_all
  simp [h1, h2]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma modeDerivation_offDiagonalBlockSqNorm_lemma_19 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) =
      ∑ j, X (Sum.inl j.1) * _root_.GlobalTheory.PsCo.Pc1.OmP ε x j := by
  simp [_root_.GlobalTheory.PsCo.Pc1.rP, _root_.GlobalTheory.PsCo.Pc1.OmP, map_sum, Derivation.leibniz,
    modeDerivation_offDiagonalEntry_lemma_21]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma pencilModeDerivation_embedding_lemma_16 (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε) (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x (_root_.GlobalTheory.PsCo.Pc1.A.i2 L s) =
      _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε x s) := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.i2, pencilModeDerivation_lambdaPoly_lemma_7, lambdaModeDerivation_entryPoly_lemma_8]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma lambdaPoly_mem_lambdaSquaresIdealPolyM_lemma_20 {g : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L}
    (hg : g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JL L) :
    _root_.GlobalTheory.PsCo.Pc1.A.inM n L g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
  have h : Ideal.map (_root_.GlobalTheory.PsCo.Pc1.A.inM n L) (_root_.GlobalTheory.PsCo.Pc1.A.JL (n := n) L) =
      _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.JL, _root_.GlobalTheory.PsCo.Pc1.A.JM, Ideal.map_span, ← Set.range_comp]
    simp [Function.comp_def, map_pow]
  exact h ▸ Ideal.mem_map_of_mem _ hg

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma weight_modeDerivation_sub_mem_lemma_11 (M : ℕ) (m : Fin L → _root_.GlobalTheory.PsCo.Pc1.Poly n)
    (c : Fin L → _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ)
    (hc : ∀ l x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (m l) = ∑ y, C (c l x y) * X (Sum.inl y.1))
    (i : _root_.GlobalTheory.PsCo.Pc1.Mode ε) :
    _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m)) +
        _root_.GlobalTheory.PsCo.Pc1.A.muM n L *
          _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (_root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε)) *
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) -
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) *
        ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) i j *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L := by
  have hP0 := _root_.GlobalTheory.PsCo.Cw2a.t_dual_prod (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε i)
    (fun l => _root_.GlobalTheory.PsCo.Pc1.A.laL n l)
    (fun l => _root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)) (_root_.GlobalTheory.PsCo.Pc1.A.JL L)
    (fun l => lambdaModeDerivation_variable_lemma_10 ε i l) (fun l => Ideal.subset_span ⟨l, rfl⟩)
  have hk : _root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.detbP n) = 0 :=
    _root_.GlobalTheory.PsCo.Cw2a.modeDerivation_det_eq_zero ε i
  have hdM : _root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) = 0 := by
    simp [Derivation.leibniz_pow, hk]
  have hE : _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
        _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m) := by
    rw [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, Derivation.leibniz, lambdaModeDerivation_entryPoly_lemma_8, hdM]
    simp
  have hB : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c i j * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (X (Sum.inl j.1)) =
      ∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
        _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)) := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [lambdaModeDerivation_entryPoly_lemma_8, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [_root_.GlobalTheory.PsCo.Pc1.A.inL, mul_assoc]
  have hA : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L i j) *
        _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) =
      _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) := by
    rw [modeDerivation_offDiagonalBlockSqNorm_lemma_19]
    simp [map_sum, _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, _root_.GlobalTheory.PsCo.Pc1.A.i2, mul_comm]
  have hsplit : ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) i j *
        _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) =
      _root_.GlobalTheory.PsCo.Pc1.A.muM n L * ∑ j, _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L i j) *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) +
        _root_.GlobalTheory.PsCo.Pc1.A.inM n L
          (∑ j, _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c i j * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (X (Sum.inl j.1))) := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.Zm, add_mul, Finset.sum_add_distrib, Finset.mul_sum, map_sum, map_mul, mul_assoc]
    rfl
  rw [hsplit, pencilModeDerivation_embedding_lemma_16, hA, hB, pencilModeDerivation_lambdaPoly_lemma_7, hE]
  have key : _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
          _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m)) +
        _root_.GlobalTheory.PsCo.Pc1.A.muM n L *
          _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) *
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) -
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) *
        (_root_.GlobalTheory.PsCo.Pc1.A.muM n L *
            _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.dM ε i (_root_.GlobalTheory.PsCo.Pc1.rP ε)) +
          _root_.GlobalTheory.PsCo.Pc1.A.inM n L (∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
            _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)))) =
      _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M) *
        (_root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m) -
          _root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct m * ∑ l, _root_.GlobalTheory.PsCo.Pc1.A.laL n l *
            _root_.GlobalTheory.PsCo.Pc1.A.dL L ε i (_root_.GlobalTheory.PsCo.Pc1.A.inL n L (m l)))) := by
    simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, map_mul, map_sub]
    ring
  rw [key]
  exact lambdaPoly_mem_lambdaSquaresIdealPolyM_lemma_20 (Ideal.mul_mem_left _ _ hP0)

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma optionEquivLeft_rename_some_eq_C_lemma_23 (a : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    optionEquivLeft ℂ _ (rename some a) = Polynomial.C a := by
  have h : ((optionEquivLeft ℂ (Fin L ⊕ _root_.GlobalTheory.PsCo.Pc1.A.EntIdx n)).toAlgHom.comp (rename some)) =
      (Polynomial.CAlgHom : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L →ₐ[ℂ] _) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [optionEquivLeft_X_some]
  exact congrArg (fun f => f a) h

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_lambdaPoly_mul_lemma_18 (a : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.inM n L a * F) =
      a * _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.inM, optionEquivLeft_rename_some_eq_C_lemma_23]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma lambdaCoeff_mul_variable_sq_lemma_22 (G : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) (i : Fin L) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (G * _root_.GlobalTheory.PsCo.Pc1.A.laL n i ^ 2) = 0 := by
  simp only [_root_.GlobalTheory.PsCo.Pc1.A.exL, _root_.GlobalTheory.PsCo.Pc1.A.laL, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, map_pow, sumAlgEquiv_X_inl]
  simp only [LinearMap.coe_restrictScalars, MvPolynomial.lcoeff_apply]
  rw [X_pow_eq_monomial, coeff_mul_monomial', if_neg]
  intro h
  have := h i
  simp [_root_.GlobalTheory.PsCo.Pc1.A.allOnes] at this

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_eq_zero_of_mem_lambdaSquares_lemma_12 {g : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L}
    (hg : g ∈ _root_.GlobalTheory.PsCo.Pc1.A.JM L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k g) = 0 := by
  rw [_root_.GlobalTheory.PsCo.Pc1.A.JM, Ideal.mem_span_range_iff_exists_fun] at hg
  obtain ⟨f, rfl⟩ := hg
  simp only [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← map_pow, mul_comm, muCoeff_lambdaPoly_mul_lemma_18, mul_comm, lambdaCoeff_mul_variable_sq_lemma_22]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma sumAlgEquiv_rename_inr_eq_C_lemma_25 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) :
    sumAlgEquiv ℂ (Fin L) (_root_.GlobalTheory.PsCo.Pc1.A.EntIdx n) (rename Sum.inr s) = C s := by
  have h := sumAlgEquiv_comp_rename_inr ℂ (Fin L) (_root_.GlobalTheory.PsCo.Pc1.A.EntIdx n)
  exact congrArg (fun f => f s) h

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma extractCoeff_inl_mul (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (G : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.inL n L s * G) =
      s * _root_.GlobalTheory.PsCo.Pc1.A.exL n L G := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.exL, _root_.GlobalTheory.PsCo.Pc1.A.inL, sumAlgEquiv_rename_inr_eq_C_lemma_25, coeff_C_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_pderiv_mu_lemma_13 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (pderiv none F)) =
      (k + 1 : _root_.GlobalTheory.PsCo.Pc1.Poly n) *
        _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L (k + 1) F) := by
  rw [_root_.GlobalTheory.PsCo.Cw2a.t_coefM_pderiv]
  simp only [Algebra.smul_def, map_add, map_natCast, map_one, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [show ((k : _root_.GlobalTheory.PsCo.Pc1.A.PolyL n L) + 1) =
      _root_.GlobalTheory.PsCo.Pc1.A.inL n L ((k : _root_.GlobalTheory.PsCo.Pc1.Poly n) + 1) by simp, extractCoeff_inl_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_embedding_mul_lemma_14 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.i2 L s * F)) =
      s * _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F) := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.i2, muCoeff_lambdaPoly_mul_lemma_18, extractCoeff_inl_mul]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_modeDerivation_lemma_15 {ε : Fin n → Bool} (x : _root_.GlobalTheory.PsCo.Pc1.Mode ε)
    (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x F)) =
      _root_.GlobalTheory.PsCo.Pc1.dM ε x
        (_root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F)) := by
  rw [_root_.GlobalTheory.PsCo.Cw2a.coefM_dMu, _root_.GlobalTheory.PsCo.Cw2a.exL_dL_holds]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_zero_mu_mul_lemma_26 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L 0 (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F) = 0 := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.muM]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma muCoeff_succ_mu_mul_lemma_27 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.coefM n L (k + 1) (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F) =
      _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F := by
  simp [_root_.GlobalTheory.PsCo.Pc1.A.coefM, _root_.GlobalTheory.PsCo.Pc1.A.muM]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma coeff_mu_mul_lemma_17 (F : _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (_root_.GlobalTheory.PsCo.Pc1.A.muM n L * F)) =
      _root_.GlobalTheory.PsCo.Pc1.prev
        (fun k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k F)) k := by
  cases k with
  | zero => simp [muCoeff_zero_mu_mul_lemma_26, _root_.GlobalTheory.PsCo.Pc1.prev]
  | succ k => simp [muCoeff_succ_mu_mul_lemma_27, _root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_const_mul_lemma_4 (s : _root_.GlobalTheory.PsCo.Pc1.Poly n) (f : ℕ → _root_.GlobalTheory.PsCo.Pc1.Poly n) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun k => s * f k) k = s * _root_.GlobalTheory.PsCo.Pc1.prev f k := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} (ε : Fin n → Bool) in
private lemma koszulRecursion_solvable_of_product_lemma (M : ℕ) (m : Fin L → _root_.GlobalTheory.PsCo.Pc1.Poly n)
    (c : Fin L → _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ)
    (hc : ∀ l x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (m l) = ∑ y, C (c l x y) * X (Sum.inl y.1)) :
    ∃ p q, _root_.GlobalTheory.PsCo.Pc1.IsKoszul ε p q ∧
      p (_root_.GlobalTheory.PsCo.Pc1.nMode ε) = _root_.GlobalTheory.PsCo.Pc1.topP ε M (∏ l, m l) := by
  set Z := _root_.GlobalTheory.PsCo.Pc1.A.Zm ε L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L) (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c) with hZ
  set w := _root_.GlobalTheory.PsCo.Pc1.A.inM n L (_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m) with hw
  set a : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L :=
    fun j => _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inr j.1)) with ha
  set b : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.A.PolyM n L :=
    fun j => _root_.GlobalTheory.PsCo.Pc1.A.i2 L (X (Sum.inl j.1)) with hb
  have h1 : ∀ i j, pderiv none (Z i j) = _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (a j) := by
    intro i j
    simp [hZ, ha, _root_.GlobalTheory.PsCo.Pc1.A.Zm, Derivation.leibniz, pderiv_mu_lambdaPoly_lemma_5, pderiv_mu_muVariable_lemma_6,
      _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, _root_.GlobalTheory.PsCo.Pc1.A.i2, pencilModeDerivation_lambdaPoly_lemma_7,
      lambdaModeDerivation_entryPoly_lemma_8, _root_.GlobalTheory.PsCo.Pc1.OmP]
  have h2 : ∀ h i j, _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε h (Z i j) = _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε i (Z h j) := by
    intro h i j
    simp only [hZ, _root_.GlobalTheory.PsCo.Pc1.A.Zm, Derivation.leibniz, pencilModeDerivation_muVariable_lemma_9,
      pencilModeDerivation_lambdaPoly_lemma_7, _root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix, lambdaModeDerivation_entryPoly_lemma_8,
      _root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix, map_add, map_sum, lambdaModeDerivation_variable_lemma_10, smul_zero, add_zero, smul_eq_mul,
      mul_zero]
    simp only [MvPolynomial.derivation_C, mul_zero, smul_zero, zero_add, add_zero, Finset.sum_const_zero, map_zero,
      smul_eq_mul, _root_.GlobalTheory.PsCo.Pc1.OmP]
    rw [_root_.GlobalTheory.PsCo.DMComm.dM_comm ε h i]
  have h3 : pderiv none w = 0 := pderiv_mu_lambdaPoly_lemma_5 _
  have h5 : _root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε) = ∑ j, b j * a j := by
    simp [hb, ha, _root_.GlobalTheory.PsCo.Pc1.rP, map_sum]
  have hmem := _root_.GlobalTheory.weighted_det_divergence_mem_ideal (fun x => _root_.GlobalTheory.PsCo.Pc1.A.dMu L ε x) (pderiv none)
    (_root_.GlobalTheory.PsCo.Pc1.A.JM L) Z a b w (_root_.GlobalTheory.PsCo.Pc1.A.muM n L)
    (_root_.GlobalTheory.PsCo.Pc1.A.i2 L (_root_.GlobalTheory.PsCo.Pc1.rP ε)) h1 h2 h3
    (fun i => weight_modeDerivation_sub_mem_lemma_11 ε M m c hc i) h5
  obtain ⟨d1, d2, d3⟩ := _root_.GlobalTheory.coefM_pencil (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L)
    (_root_.GlobalTheory.PsCo.Pc1.A.pencilConstantPartMatrix ε c)
  have e1 : ∀ k, Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) < k → _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k Z.det = 0 := d1
  have e2 : _root_.GlobalTheory.PsCo.Pc1.A.coefM n L (Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε)) Z.det =
      (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L).det := d2
  have e3 : ∀ k x y, Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) ≤ k →
      _root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (Z.adjugate y x) = 0 := d3
  have hN : _root_.GlobalTheory.PsCo.Pc1.nMode ε = Fintype.card (_root_.GlobalTheory.PsCo.Pc1.Mode ε) := rfl
  refine ⟨fun k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (w * Z.det)),
    fun x k => _root_.GlobalTheory.PsCo.Pc1.A.exL n L (_root_.GlobalTheory.PsCo.Pc1.A.coefM n L k (w * ∑ j, Z.adjugate j x * a j)),
    ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
  · have hk := coeff_eq_zero_of_mem_lambdaSquares_lemma_12 hmem k
    simp only [map_sub, map_add, map_sum, coeff_pderiv_mu_lemma_13, coeff_embedding_mul_lemma_14, coeff_modeDerivation_lemma_15, mul_assoc,
      pencilModeDerivation_embedding_lemma_16, coeff_mu_mul_lemma_17, shift_const_mul_lemma_4] at hk
    simp only [← mul_assoc] at hk ⊢
    linear_combination hk
  · rw [hN] at hk
    simp only [hw, muCoeff_lambdaPoly_mul_lemma_18]
    rw [e1 k hk, mul_zero, map_zero]
  · rw [hN] at hk
    simp only [Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [hw, ha, _root_.GlobalTheory.PsCo.Pc1.A.i2, AlgHom.comp_apply]
    rw [mul_comm (Z.adjugate j x), ← mul_assoc, ← map_mul, muCoeff_lambdaPoly_mul_lemma_18, e3 k x j hk, mul_zero, map_zero]
  · have hdet : (_root_.GlobalTheory.PsCo.Pc1.A.pencilDerivativePartMatrix ε L).det =
        _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det := by
      rw [AlgHom.map_det]; rfl
    simp only [hN, hw, muCoeff_lambdaPoly_mul_lemma_18]
    rw [e2, hdet]
    have hprod := _root_.GlobalTheory.PsCo.Cw2a.t_exL_dual (L := L) m
      (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M * (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det)
    rw [show _root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight M m * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det =
        (∏ i, (1 + _root_.GlobalTheory.PsCo.Pc1.A.laL n i * _root_.GlobalTheory.PsCo.Pc1.A.inL n L (m i))) *
          _root_.GlobalTheory.PsCo.Pc1.A.inL n L
            (_root_.GlobalTheory.PsCo.Pc1.detbP n ^ M * (_root_.GlobalTheory.PsCo.Pc1.OmP ε).det) by
      simp only [_root_.GlobalTheory.PsCo.Pc1.A.pencilDeterminantWeight, _root_.GlobalTheory.PsCo.Pc1.A.dualNumberFactorsProduct, map_mul]; ring, hprod]
    simp only [_root_.GlobalTheory.PsCo.Pc1.topP]
    ring

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_zero_lemma_2 (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun _ => (0 : _root_.GlobalTheory.PsCo.Pc1.Poly n)) k = 0 := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in
variable {n L : ℕ} in
private lemma shift_add_lemma_3 (f g : ℕ → _root_.GlobalTheory.PsCo.Pc1.Poly n) (k : ℕ) :
    _root_.GlobalTheory.PsCo.Pc1.prev (fun k => f k + g k) k =
      _root_.GlobalTheory.PsCo.Pc1.prev f k + _root_.GlobalTheory.PsCo.Pc1.prev g k := by
  cases k <;> simp [_root_.GlobalTheory.PsCo.Pc1.prev]

open MvPolynomial in
variable {n L : ℕ} in

theorem _root_.GlobalTheory.PsCo.Pc1.A.stAlg : _root_.GlobalTheory.PsCo.Pc1.StAlg := by
  intro n ε M P hP
  have hP' : P ∈ Submodule.span ℂ (Submonoid.closure
      {P : _root_.GlobalTheory.PsCo.Pc1.Poly n | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))} : Set _) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have hgen : ∀ i : Fin l.length, ∃ c : _root_.GlobalTheory.PsCo.Pc1.Mode ε → _root_.GlobalTheory.PsCo.Pc1.Mode ε → ℂ,
        ∀ x, _root_.GlobalTheory.PsCo.Pc1.dM ε x (l.get i) = ∑ y, C (c x y) * X (Sum.inl y.1) := by
      intro i
      obtain ⟨a, b, hab, he⟩ := hl _ (List.get_mem l i)
      rw [he]
      exact _root_.GlobalTheory.PsCo.Cw2a.dM_block_entries ε a b hab
    choose c hc using hgen
    obtain ⟨p, q, hpq, htop⟩ := koszulRecursion_solvable_of_product_lemma ε M (fun i => l.get i) c hc
    refine ⟨p, q, hpq, ?_⟩
    rw [htop, ← Fin.prod_ofFn, List.ofFn_get]
  | zero =>
    refine ⟨fun _ => 0, fun _ _ => 0, ⟨fun k => ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    · simp [shift_zero_lemma_2]
    · simp [_root_.GlobalTheory.PsCo.Pc1.topP]
  | add x y _ _ hx hy =>
    obtain ⟨p₁, q₁, ⟨r₁, s₁, t₁⟩, e₁⟩ := hx
    obtain ⟨p₂, q₂, ⟨r₂, s₂, t₂⟩, e₂⟩ := hy
    refine ⟨fun k => p₁ k + p₂ k, fun x k => q₁ x k + q₂ x k,
      ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
    · have h₁ := r₁ k
      have h₂ := r₂ k
      simp only [map_add, shift_add_lemma_3, mul_add, Finset.sum_add_distrib] at h₁ h₂ ⊢
      linear_combination h₁ + h₂
    · simp [s₁ k hk, s₂ k hk]
    · simp [t₁ x k hk, t₂ x k hk]
    · simp only [e₁, e₂, _root_.GlobalTheory.PsCo.Pc1.topP]
      ring
  | smul r x _ hx =>
    obtain ⟨p₁, q₁, ⟨r₁, s₁, t₁⟩, e₁⟩ := hx
    refine ⟨fun k => C r * p₁ k, fun x k => C r * q₁ x k,
      ⟨fun k => ?_, fun k hk => ?_, fun x k hk => ?_⟩, ?_⟩
    · have h₁ := r₁ k
      simp only [Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul, shift_const_mul_lemma_4]
      simp only [mul_add, Finset.sum_add_distrib] at h₁ ⊢
      have hc : ∀ x : _root_.GlobalTheory.PsCo.Pc1.Mode ε,
          _root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) *
              (C r * _root_.GlobalTheory.PsCo.Pc1.prev (q₁ x) k) =
            C r * (_root_.GlobalTheory.PsCo.Pc1.dM ε x (_root_.GlobalTheory.PsCo.Pc1.rP ε) *
              _root_.GlobalTheory.PsCo.Pc1.prev (q₁ x) k) := fun _ => by ring
      simp only [mul_zero, Finset.sum_const_zero, add_zero, hc, ← Finset.mul_sum]
      linear_combination C r * h₁
    · simp [s₁ k hk]
    · simp [t₁ x k hk]
    · simp only [e₁, _root_.GlobalTheory.PsCo.Pc1.topP, smul_eq_C_mul]
      ring

end GlobalTheory.PsCo.Pc1.A

end
end
