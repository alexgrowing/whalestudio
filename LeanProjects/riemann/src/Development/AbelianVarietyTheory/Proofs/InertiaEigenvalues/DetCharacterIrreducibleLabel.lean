import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed

noncomputable section

namespace GlobalTheory.GLq.LabelDet

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Formalism.CyclotomicNorms Polynomial
open scoped Classical ComplexOrder

variable {g : ℕ} [hg : Fact g.Prime]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : G, (FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ)).character x = φ x := by
    intro x
    have : _root_.GlobalTheory.GLp.Model.chRep φ x = (φ x : ℂ) • LinearMap.id := by
      ext; simp [_root_.GlobalTheory.GLp.Model.chRep_apply]
    simp [FDRep.character, FDRep.of_ρ, this]
  refine ⟨FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ), ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

theorem level_pos : 0 < g ^ 1 - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow one_ne_zero hg.out.one_lt)

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.theta_gen_pow (L : _root_.GlobalTheory.GLq.LabelDatum g) {x : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hx : x ^ (g ^ 1 - 1) = 1) (n : ℕ) :
    _root_.GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) =
      L.teich x ^ n :=
  _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos hx n

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.gen_one_mem (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 := by
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.GLp.Model.exists_gen L
  exact ⟨u, hu⟩

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.det_inPar (a b : ℕ) (M : _root_.GlobalTheory.GLq.Mt g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a M) :
    M.det = (_root_.GlobalTheory.GLq.tl a M).det * (_root_.GlobalTheory.GLq.br a b M).det := by
  have key : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (_root_.GlobalTheory.GLq.tl a M)
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0 (_root_.GlobalTheory.GLq.br a b M) := by
    ext (i | i) (j | j)
    · show M (Fin.castAdd b i) (Fin.castAdd b j) = _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j
      have hi := i.isLt
      have hj := j.isLt
      unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dif_pos ⟨by omega, by omega⟩]
      rfl
    · simp
    · exact h _ _ (by simp) (by simp)
    · simp [_root_.GlobalTheory.GLq.br, _root_.Formalism.MainNotions.ArithmeticCylinders.entN, Fin.natAdd]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, key, Matrix.det_fromBlocks_zero₂₁]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_toG {n : ℕ} (M : _root_.GlobalTheory.GLq.Mt g n) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG M) : (ZMod g)ˣ) : ZMod g) = M.det := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dif_pos ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.GeneralLinearGroup.val_det_apply]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_par (a b : ℕ) (p : _root_.GlobalTheory.GLq.Gn g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a (p : _root_.GlobalTheory.GLq.Mt g (a + b))) :
    Matrix.GeneralLinearGroup.det p =
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) *
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) := by
  have hdet := _root_.GlobalTheory.GLq.LabelDet.det_inPar a b _ h
  have hp := (Matrix.GeneralLinearGroup.det p).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hp
  rw [hdet] at hp
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
  apply Units.ext
  rw [Units.val_mul, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h1, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h2,
    Matrix.GeneralLinearGroup.val_det_apply, ← hdet]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.toG_one {n : ℕ} : _root_.GlobalTheory.GLq.toG (1 : _root_.GlobalTheory.GLq.Mt g n) = 1 := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dif_pos isUnit_one]
  exact Units.ext (by simp)

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j h1 h2 =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  simp [br, entN, Matrix.one_apply, Fin.ext_iff]

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp [tl, entN, Matrix.one_apply, Fin.ext_iff, hi, hj]

def PosMul (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∃ r : Gn g n → ℂ, (∀ x, 0 ≤ r x) ∧ 0 < r 1 ∧
    ∀ x, F x = r x * ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)

end GlobalTheory.GLq.LabelDet
