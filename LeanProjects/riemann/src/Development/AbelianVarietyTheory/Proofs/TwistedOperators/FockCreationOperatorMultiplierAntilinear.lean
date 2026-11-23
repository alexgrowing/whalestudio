import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem map_inv_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.adjugate.map f = (M.map f).adjugate := by
    have := RingHom.map_adjugate f M; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (M.map f).det = f M.det := by
    have := RingHom.map_det f M; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem formAt_eq_omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.OrientedHeis.formAt S T τ x y = GlobalTheory.VacUnique.omAt S T τ x y := by
  unfold GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt
  congr 3
  rw [gramAt, gramAt, ← map_inv_ringHom]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem omF_eq {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B z e = GlobalTheory.VacUnique.omO S T (fmR A B z) (fmR A B e) := by
  rw [GlobalTheory.VacUnique.omO_apply]
  exact Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _

theorem cplxO_smulC' {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum' {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem fmR_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (I • z) = GlobalTheory.VacUnique.jO S T A.cart B.cart (fmR A B z) := by
  funext τ
  show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))
  have hs := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1
  have ht := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1
  unfold fockMat
  rw [cplxO_sum']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]
  have e1 : ((I • z) τ i j).re = -(z τ i j).im := by simp
  have e2 : ((I • z) τ i j).im = (z τ i j).re := by simp
  rw [e1, e2]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]
  abel

theorem fmR_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (z + w) = fmR A B z + fmR A B w := by
  funext τ
  show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
  simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel

theorem fmR_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (c • z) = c • fmR A B z := by
  funext τ
  show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
  simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_smul]

theorem omF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (z + w) e = omF A B z e + omF A B w e := by
  rw [omF_eq, omF_eq, omF_eq, fmR_add, map_add, LinearMap.add_apply]

theorem omF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (c • z) e = c * omF A B z e := by
  rw [omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem omF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) e = -omF A B z (I • e) := by
  obtain ⟨hJJ, -, hinv, -⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
  rw [omF_eq, omF_eq, fmR_I, fmR_I]
  set J := GlobalTheory.VacUnique.jO S T A.cart B.cart
  set x := fmR A B z
  set y := fmR A B e
  have hy : y = -J (J y) := by rw [hJJ, neg_neg]
  conv_lhs => rw [hy]
  rw [map_neg, hinv]

theorem omF_I_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) (I • e) = omF A B z e := by
  rw [omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]
  have : fmR A B (-e) = -fmR A B e := by
    have h := fmR_smul A B (-1) e
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [this, map_neg, neg_neg]

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem gD_add (c : ι → ℝ) (z w e : VCx ι a b) : gD c (z + w) e = gD c z e + gD c w e := by
  simp only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem gD_smul (c : ι → ℝ) (r : ℝ) (z e : VCx ι a b) : gD c (r • z) e = r * gD c z e := by
  simp only [gD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  ring

theorem gD_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) e = -gD c z (I • e) := by
  simp only [gD, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

theorem gD_I_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) (I • e) = gD c z e := by
  simp only [gD]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

end GlobalTheory.FockTransl.Jet

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem lamF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z w : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (z + w) = lamF A B l z + lamF A B l w := by
  simp only [lamF, omF_add, gD_add]
  push_cast
  ring

theorem lamF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (r : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (r • z) = r * lamF A B l z := by
  simp only [lamF, omF_smul, gD_smul]
  push_cast
  ring

theorem lamF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (I • z) = -I * lamF A B l z := by
  simp only [lamF]
  rw [omF_I_I, omF_I, gD_I_I, gD_I]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) +
    (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq

theorem lamF_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  intro D S T A B l
  refine ⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩
  have e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a) := by
    funext τ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im t]
    ring
  have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp
  rw [e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]
  ring

end GlobalTheory.FockTransl.Jet

end
