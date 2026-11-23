import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt

noncomputable section

namespace Formalism.L2.LamCM

open MvPolynomial IsLocalRing

section Subst

variable {B : Type} {m : B → ℕ}

theorem bind₁_eq_self_of {σ R : Type} [CommSemiring R] (f : σ → MvPolynomial σ R) (hf : ∀ v, f v = X v)
    (P : MvPolynomial σ R) : bind₁ f P = P := by
  rw [show f = X from funext hf, bind₁_X_left]
  rfl

theorem substFr_one {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) :
    substFr (fun b => (1 : Matrix (Fin (m b)) (Fin (m b)) R)) P = P := by
  unfold substFr
  apply bind₁_eq_self_of
  rintro ⟨b, i, k⟩
  simp [Matrix.one_apply]

theorem substFr_substFr {R : Type} [CommRing R] (U U' : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) : substFr U (substFr U' P) = substFr (fun b => U b * U' b) P := by
  unfold substFr
  rw [bind₁_bind₁]
  refine congrArg (fun g => bind₁ g P) (funext fun v => ?_)
  simp only [map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem evalFr_substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    evalFr (substFr U P) Y = evalFr P (fun b => (U b).transpose * Y b) := by
  unfold evalFr substFr
  show eval₂Hom (RingHom.id R) _ (bind₁ _ P) = eval₂Hom (RingHom.id R) _ P
  rw [eval₂Hom_bind₁]
  refine congrArg (fun g => eval₂Hom (RingHom.id R) g P) (funext fun v => ?_)
  simp [Matrix.mul_apply, mul_comm]

theorem substFr_C_mul {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (a : R)
    (P : MvPolynomial (FrVar m) R) : substFr U (C a * P) = C a * substFr U P := by
  unfold substFr
  rw [map_mul, bind₁_C_right]

theorem map_substFr {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) :
    MvPolynomial.map f (substFr U P) = substFr (fun b => (U b).map f) (MvPolynomial.map f P) := by
  unfold substFr
  rw [map_bind₁]
  refine congrArg (fun g => bind₁ g (MvPolynomial.map f P)) (funext fun v => ?_)
  simp [map_sum, map_mul, map_C, map_X]

theorem evalFr_C_mul {R : Type} [CommRing R] (a : R) (P : MvPolynomial (FrVar m) R)
    (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : evalFr (C a * P) Y = a * evalFr P Y := by
  unfold evalFr
  simp

end Subst

theorem subst_eval : SubstEval := by
  intro R _ B _ m P U
  refine ⟨fun Y => evalFr_substFr U P Y, fun hU => ?_, substFr_one P⟩
  rw [substFr_substFr]
  have h : (fun b => U b * (U b)⁻¹) = fun b => (1 : Matrix (Fin (m b)) (Fin (m b)) R) :=
    funext fun b => Matrix.mul_nonsing_inv _ (hU b)
  rw [h, substFr_one]

theorem large_residue_extension_lemma : LemmaG := LemmaG_of largeResidueExtension

theorem coeff_integral_local : CoeffIntegralLoc := by
  intro V K' _ _ _ _ _ _ B _ m G U c τ hV hfin hτ hU hc hG μ
  classical
  have hUu : ∀ b, IsUnit (U b).det := fun b => isUnit_iff_ne_zero.mpr (hU b)
  set P : MvPolynomial (FrVar m) K' := C τ⁻¹ * substFr (fun b => (U b)⁻¹) G with hP
  have hPc : ∀ ν, coeff ν P ∈ Set.range (algebraMap V K') := by
    refine large_residue_extension_lemma V K' B m P hV hfin ?_
    intro W KW _ _ _ _ _ _ _ f hW hWf hloc hcomp X hX
    obtain ⟨w, hw⟩ := hG W KW f hW hWf hloc hcomp
      (fun b => (((U b)⁻¹).map f).transpose * (X b).map (algebraMap W KW)) X hX (by
        intro b
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hUu b),
          Matrix.map_one _ (map_zero f) (map_one f), Matrix.transpose_one, Matrix.one_mul])
    refine ⟨w, ?_⟩
    rw [hP, map_mul, map_C, map_substFr, evalFr_C_mul, evalFr_substFr]
    rw [hw, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hτ, map_one, one_mul]
  have hS := substGauss V K' B m P U c hPc hc μ
  have hsub : substFr U P = C τ⁻¹ * G := by
    rw [hP, substFr_C_mul, (subst_eval K' B m G U).2.1 hUu]
  obtain ⟨w, hw⟩ := hS
  refine ⟨w, ?_⟩
  rw [hsub, coeff_C_mul] at hw
  rw [hw]
  field_simp

end Formalism.L2.LamCM
