import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueSquareIntegrableLevelZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Pr

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_mul (x y : Pr V) : (x * y).1 = x.1 * y.1 := rfl

theorem pr_fst_algebraMap (a : ℂ) : (algebraMap ℂ (Pr V) a).1 = algebraMap ℂ (Module.End ℂ V) a := rfl

def sendsTo (U : Submodule ℂ V) (v : V) : Submodule ℂ (Pr V) where
  carrier := {x | x.1 v ∈ U}
  zero_mem' := by show (0 : Module.End ℂ V) v ∈ U; simp
  add_mem' := by
    intro x y hx hy
    show (x.1 + y.1) v ∈ U
    rw [LinearMap.add_apply]; exact U.add_mem hx hy
  smul_mem' := by
    intro a x hx
    show (a • x.1) v ∈ U
    rw [LinearMap.smul_apply]; exact U.smul_mem a hx

theorem sendsTo_alg_mul_alg (U : Submodule ℂ V) (v : V) {x : Pr V} (hx : x ∈ sendsTo U v) (a b : ℂ) :
    algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b ∈ sendsTo U v := by
  show (algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b).1 v ∈ U
  rw [pr_fst_mul, pr_fst_mul, pr_fst_algebraMap, pr_fst_algebraMap, Module.End.mul_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  exact U.smul_mem a (U.smul_mem b hx)

end Pr

section Num

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem UUw_mem {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Um (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Um, 𝒜.algebraMap_mem]

theorem star_entSub {𝒜 : StarSubalgebra ℂ A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ entSub 𝒜) : star M ∈ entSub 𝒜 := by
  intro i j
  rw [Matrix.star_apply]
  exact star_mem (hM j i)

theorem mem_bot_alg {x : A} (hx : x ∈ (⊥ : StarSubalgebra ℂ A)) : ∃ a : ℂ, x = algebraMap ℂ A a := by
  rw [StarSubalgebra.mem_bot] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end Num

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem QQi_castSucc' (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l : Fin P.r) (Y : ℂ) :
    QQi L st l.castSucc Y = (Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have h : ∀ Y' : ℂ, tprod L Y' l.val = tprod L Y' (l.val + 1) * Ts (site L l) Y' := fun Y' => by
    rw [tprod, dif_pos l.isLt]
  unfold QQi
  rw [Fin.val_castSucc, Fin.val_succ, h, h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem diag_comm {A : Type*} [Ring A] {f : A} {M : Matrix (Fin 2) (Fin 2) A} (h : ∀ i j, Commute f (M i j)) :
    Matrix.diagonal (fun _ => f) * M = M * Matrix.diagonal (fun _ => f) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem commute_inv_of {A : Type*} [Ring A] {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : Commute f x) :
    Commute fi x := by
  show fi * x = x * fi
  calc fi * x = fi * x * (f * fi) := by rw [h1, mul_one]
    _ = fi * (f * x) * fi := by rw [h.eq]; simp only [mul_assoc]
    _ = x * fi := by rw [← mul_assoc, h2, one_mul]

theorem waveQQ_castSucc (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (hAL : IsActualLevel X L) (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (hC : ∀ Y a b, Commute (mkP Wv Wv') (QQi L st l.succ Y a b)) :
    WaveQQ (QQi L st l.castSucc) (mkP Wv Wv') (mkP Wv' Wv) s := by
  intro Y
  obtain ⟨⟨h1, h2, h3⟩, hc, hci, hp⟩ :=
    Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hAL l s Wv Wv' hW hW'
  have hT : ∀ Y' : ℂ, Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') =
      Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
    intro Y'
    obtain ⟨-, hUiU, hE⟩ := Formalism.YangianSpanCharacter.Final.T_PlaneWave ℂ (Pr (RadSp P.k P.r z z' π π')) (site L l).p (site L l).c
      (site L l).ci (mkP Wv Wv') s Y' hc hci hp
    calc Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv')
        = Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * (Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
          rw [hUiU, Matrix.mul_one]
      _ = (Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          unfold Ts; rw [hE]
  have hDf : (Matrix.diagonal (fun _ : Fin 2 => mkP Wv Wv'))ᴴ = Matrix.diagonal (fun _ => mkP Wv' Wv) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  have ha := congrArg Matrix.conjTranspose (hT (star Y))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDf] at ha
  have hci' : ∀ a b, Commute (mkP Wv' Wv) (QQi L st l.succ Y a b) := fun a b =>
    commute_inv_of h1 h2 (hC Y a b)
  have hb : Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv') =
      QQi L st l.succ Y := by
    rw [diag_comm hci', Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h2]
    rw [show (Matrix.diagonal fun _ : Fin 2 => (1 : Pr (RadSp P.k P.r z z' π π'))) = 1 from Matrix.diagonal_one,
      Matrix.mul_one]
  rw [QQi_castSucc']
  calc Matrix.diagonal (fun _ => mkP Wv' Wv) *
        ((Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y) * Matrix.diagonal (fun _ => mkP Wv Wv')
      = (Matrix.diagonal (fun _ => mkP Wv' Wv) * (Ts (site L l) (star Y))ᴴ) * QQi L st l.succ Y *
          (Ts (site L l) Y * Matrix.diagonal (fun _ => mkP Wv Wv')) := by simp only [Matrix.mul_assoc]
    _ = ((Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * ((Ts (site L l) (star Y))ᴴ * Matrix.diagonal (fun _ => mkP Wv' Wv))) *
          QQi L st l.succ Y * (Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
        rw [ha, hT Y]
    _ = (Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * (Ts (site L l) (star Y))ᴴ *
          (Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv')) *
          Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb]; simp only [Matrix.mul_assoc]

end Wave

section WordWave

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem rr_io_wave (QQ : ℂ → M2 A) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (hW : IsWave f fi)
    (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    RRw QQ w * io f = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by
  obtain ⟨hVVi, -, hRR, -⟩ := Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hQ hw
  obtain ⟨h1, h2, h3⟩ := hW
  have hsfi : star fi = f := by rw [← h3, star_star]
  have e1 : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Wd11.io_mul, h2, Formalism.FourierDecayAlt.P.Wd11.io_one]
  have hUU : UUiw s w * UUw s w = (1 : SlopeTestRemainingChoices S A) := by
    have hv : io f * UUiw s w * (UUw s w * io fi) = (1 : SlopeTestRemainingChoices S A) := by
      have := hVVi; unfold Vw Viw at this; simpa only [mul_assoc] using this
    calc UUiw s w * UUw s w = (io fi * io f) * (UUiw s w * UUw s w) * (io fi * io f) := by
          rw [e1, one_mul, mul_one]
      _ = io fi * (io f * UUiw s w * (UUw s w * io fi)) * io f := by simp only [mul_assoc]
      _ = 1 := by rw [hv, mul_one, e1]
  have hsVi : star (Viw fi s w) = io f * star (UUw s w) := by
    unfold Viw
    rw [star_mul, Formalism.FourierDecayAlt.P.Wd11.io_star, hsfi]
  have hsVV : star (Viw fi s w) * star (Vw f s w) = 1 := by
    rw [← star_mul, hVVi, star_one]
  have key : RRw QQ w * Vw f s w = star (Viw fi s w) * RRw QQ w := by
    calc RRw QQ w * Vw f s w = (star (Viw fi s w) * star (Vw f s w)) * RRw QQ w * Vw f s w := by
          rw [hsVV, one_mul]
      _ = star (Viw fi s w) * (star (Vw f s w) * RRw QQ w * Vw f s w) := by simp only [mul_assoc]
      _ = star (Viw fi s w) * RRw QQ w := by rw [hRR]
  calc RRw QQ w * io f = RRw QQ w * io f * (UUiw s w * UUw s w) := by rw [hUU, mul_one]
    _ = (RRw QQ w * Vw f s w) * UUw s w := by unfold Vw; simp only [mul_assoc]
    _ = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by rw [key, hsVi]; simp only [mul_assoc]

theorem io_apply_mul (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) a b = x * M a b := by
  simp [io, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) a b = M a b * x := by
  simp [io, Matrix.mul_diagonal]

end WordWave

end Formalism.FourierDecayAlt.P5.HerD
