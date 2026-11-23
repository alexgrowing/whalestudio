import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct ContDiff ComplexOrder ComplexConjugate

namespace Formalism.IndefR.Fock.DRho

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Alg

variable (D)

theorem infPart_tmul (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (a : AF D.host.F) (e : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a ⊗ₜ[D.host.F] e := rfl

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem AF_ext {p q : AF D.host.F} (h1 : fstA D.host.F p = fstA D.host.F q) (h2 : sndA D.host.F p = sndA D.host.F q) :
    p = q := Prod.ext h1 h2

def basR (R : Type) [CommRing R] [Algebra D.host.F R] : Module.Basis (Fin 2) R (R ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis R (Eqv.basE D)

theorem decR {R : Type} [CommRing R] [Algebra D.host.F R] (x : R ⊗[D.host.F] D.host.E) :
    x = (basR D R).repr x 0 ⊗ₜ[D.host.F] (1 : D.host.E) + (basR D R).repr x 1 ⊗ₜ[D.host.F] Eqv.alphaE D := by
  have h0 : Eqv.basE D 0 = 1 := by
    first
    | exact Eqv.basE_zero D
    | exact Eqv.basE_zero
    | simp [Eqv.basE]
  conv_lhs => rw [← (basR D R).sum_repr x]
  simp [Fin.sum_univ_two, basR, Algebra.TensorProduct.basis_apply, h0, Eqv.basE_one, TensorProduct.smul_tmul']

theorem pair_eq_zero (R : Type) [CommRing R] [Algebra D.host.F R] (x y : R)
    (h : x ⊗ₜ[D.host.F] (1 : D.host.E) + y ⊗ₜ[D.host.F] Eqv.alphaE D = 0) : x = 0 ∧ y = 0 := by
  have h0 : Eqv.basE D 0 = 1 := by
    first
    | exact Eqv.basE_zero D
    | exact Eqv.basE_zero
    | simp [Eqv.basE]
  have e0 : x ⊗ₜ[D.host.F] (1 : D.host.E) = x • basR D R 0 := by
    simp [basR, Algebra.TensorProduct.basis_apply, h0, TensorProduct.smul_tmul']
  have e1 : y ⊗ₜ[D.host.F] Eqv.alphaE D = y • basR D R 1 := by
    simp [basR, Algebra.TensorProduct.basis_apply, Eqv.basE_one, TensorProduct.smul_tmul']
  rw [e0, e1] at h
  have h' := congrArg (basR D R).repr h
  simp only [map_add, map_smul, Module.Basis.repr_self, map_zero] at h'
  constructor
  · simpa using congrArg (fun f => f 0) h'
  · simpa using congrArg (fun f => f 1) h'

theorem trace_tmul {R : Type} [CommRing R] [Algebra D.host.F R] (a : R) (e : D.host.E) :
    Algebra.trace R (R ⊗[D.host.F] D.host.E) (a ⊗ₜ[D.host.F] e) =
      a * algebraMap D.host.F R (Algebra.trace D.host.F D.host.E e) := by
  have h1 : a ⊗ₜ[D.host.F] e = a • ((1 : R) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul R (R ⊗[D.host.F] D.host.E) ((1 : R) ⊗ₜ[D.host.F] e) =
      (Algebra.lmul D.host.F D.host.E e).baseChange R := by
    ext x
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem traceE_one : Algebra.trace D.host.F D.host.E 1 = 2 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [Module.finrank_eq_card_basis (Eqv.basE D), Fintype.card_fin]
  rw [← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, h2]
  norm_num

theorem traceE_alpha : Algebra.trace D.host.F D.host.E (Eqv.alphaE D) = 0 := by
  let s : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  have h := Algebra.trace_eq_of_algEquiv s (Eqv.alphaE D)
  have e : s (Eqv.alphaE D) = -Eqv.alphaE D := Eqv.star_alphaE D
  rw [e, map_neg] at h
  have h2 : (2 : D.host.F) * Algebra.trace D.host.F D.host.E (Eqv.alphaE D) = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem traceAE (c : AE D) :
    Algebra.trace (AF D.host.F) (AE D) c = 2 * (basR D (AF D.host.F)).repr c 0 := by
  conv_lhs => rw [decR D c]
  rw [map_add, trace_tmul, trace_tmul, traceE_one, traceE_alpha, (algebraMap D.host.F (AF D.host.F)).map_zero,
    mul_zero, add_zero, map_ofNat, mul_comm]

theorem infPart_dec (c : AE D) :
    infPart D c = fstA D.host.F ((basR D (AF D.host.F)).repr c 0) ⊗ₜ[D.host.F] (1 : D.host.E) +
      fstA D.host.F ((basR D (AF D.host.F)).repr c 1) ⊗ₜ[D.host.F] Eqv.alphaE D := by
  conv_lhs => rw [decR D c]
  rw [map_add, infPart_tmul, infPart_tmul]

theorem finPart_dec (c : AE D) :
    finPart D c = sndA D.host.F ((basR D (AF D.host.F)).repr c 0) ⊗ₜ[D.host.F] (1 : D.host.E) +
      sndA D.host.F ((basR D (AF D.host.F)).repr c 1) ⊗ₜ[D.host.F] Eqv.alphaE D := by
  conv_lhs => rw [decR D c]
  rw [map_add, finPart_tmul, finPart_tmul]

theorem fin_coord_zero (c : AE D) (h : finPart D c = 0) :
    sndA D.host.F ((basR D (AF D.host.F)).repr c 0) = 0 ∧ sndA D.host.F ((basR D (AF D.host.F)).repr c 1) = 0 := by
  rw [finPart_dec] at h
  exact pair_eq_zero D (Af D.host.F) _ _ h

theorem eq_zero_of_parts (c : AE D) (h1 : infPart D c = 0) (h2 : finPart D c = 0) : c = 0 := by
  have h1' := h1
  rw [infPart_dec] at h1'
  have hi := pair_eq_zero D (Ainf D.host.F) _ _ h1'
  have hf := fin_coord_zero D c h2
  have e0 : (basR D (AF D.host.F)).repr c 0 = 0 :=
    AF_ext D (by rw [hi.1, map_zero]) (by rw [hf.1, map_zero])
  have e1 : (basR D (AF D.host.F)).repr c 1 = 0 :=
    AF_ext D (by rw [hi.2, map_zero]) (by rw [hf.2, map_zero])
  rw [decR D c, e0, e1, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]

theorem finPart_cA (c : AE D) :
    finPart D (cA D c) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig (finPart D c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rw [cA_tmul, finPart_tmul, finPart_tmul, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem infPart_cA (c : AE D) :
    infPart D (cA D c) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rw [cA_tmul, infPart_tmul, infPart_tmul, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conj_gW (w : NumberField.InfinitePlace D.host.F) (a : Ainf D.host.F) : conj (Eqv.gW D w a) = Eqv.gW D w a := by
  rw [Eqv.gW_real, Complex.conj_ofReal]

theorem ofReal_re_gW (w : NumberField.InfinitePlace D.host.F) (a : Ainf D.host.F) :
    (((Eqv.gW D w a).re : ℝ) : ℂ) = Eqv.gW D w a := Complex.conj_eq_iff_re.mp (conj_gW D w a)

theorem thC_incA (ρ : D.what₂.Tau) (e : D.host.E) : Eqv.thetaC D ρ (infPart D (incA D e)) = tauE D ρ e := by
  show Eqv.thetaC D ρ (infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)) = _
  rw [infPart_tmul, map_one, Eqv.thetaC_tmul, map_one, one_mul]

theorem thC_cA (ρ : D.what₂.Tau) (c : AE D) :
    Eqv.thetaC D ρ (infPart D (cA D c)) = conj (Eqv.thetaC D ρ (infPart D c)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [cA_tmul, infPart_tmul, infPart_tmul, Eqv.thetaC_tmul, Eqv.thetaC_tmul, Eqv.tauE_star, map_mul, conj_gW]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem thC_dec (ρ : D.what₂.Tau) (c : AE D) :
    Eqv.thetaC D ρ (infPart D c) = Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 0)) +
      Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 1)) * Eqv.betaT D ρ := by
  rw [infPart_dec, map_add, Eqv.thetaC_tmul, Eqv.thetaC_tmul, map_one, mul_one]
  try rfl

theorem re_thC (ρ : D.what₂.Tau) (c : AE D) :
    (((Eqv.thetaC D ρ (infPart D c)).re : ℝ) : ℂ) = Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 0)) := by
  rw [thC_dec, Complex.add_re, Complex.mul_re, Eqv.betaT_re]
  have him : (Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 1))).im = 0 := by
    have := congrArg Complex.im (conj_gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 1)))
    simp only [Complex.conj_im] at this
    linarith
  rw [him]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  exact ofReal_re_gW D _ _

theorem psi_of_snd {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (y : AF D.host.F)
    (hy : sndA D.host.F y = 0) :
    ψ y = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
      ∑ ρ, Eqv.thetaC D ρ (fstA D.host.F y ⊗ₜ[D.host.F] (1 : D.host.E))) := by
  have e : y = pairA D.host.F (fstA D.host.F y) 0 := Prod.ext rfl hy
  rw [← hψ.2.2 (Eqv.thetaC D) (Eqv.isInfFam_thetaC D), psiInf, ← e]

theorem continuous_coord (k : Fin 2) : Continuous fun c : AE D => (basR D (AF D.host.F)).repr c k :=
  IsModuleTopology.continuous_of_linearMap ((basR D (AF D.host.F)).coord k)

theorem continuous_thC (ρ : D.what₂.Tau) : Continuous fun c : AE D => Eqv.thetaC D ρ (infPart D c) := by
  have hf : Continuous (fstA D.host.F) := continuous_fst
  have e : (fun c : AE D => Eqv.thetaC D ρ (infPart D c)) = fun c =>
      Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 0)) +
        Eqv.gW D (Eqv.plW D ρ) (fstA D.host.F ((basR D (AF D.host.F)).repr c 1)) * Eqv.betaT D ρ := by
    funext c; exact thC_dec D ρ c
  rw [e]
  exact ((Eqv.continuous_gW D _).comp (hf.comp (continuous_coord D 0))).add
    (((Eqv.continuous_gW D _).comp (hf.comp (continuous_coord D 1))).mul continuous_const)

end Alg

section Chart

variable {m n : ℕ}

abbrev V (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Fin m → Fin n → ℂ

def emb (y : D.what₂.Tau → ℂ) : AE D :=
  pairA D.host.F (Eqv.preA D y 0) 0 ⊗ₜ[D.host.F] (1 : D.host.E) +
    pairA D.host.F (Eqv.preA D y 1) 0 ⊗ₜ[D.host.F] Eqv.alphaE D

theorem infPart_emb (y : D.what₂.Tau → ℂ) : infPart D (emb y) = Eqv.splitInv D y := by
  simp only [emb, map_add, infPart_tmul]
  rfl

theorem finPart_emb (y : D.what₂.Tau → ℂ) : finPart D (emb y) = 0 := by
  rw [emb, map_add, finPart_tmul, finPart_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) + (0 : Af D.host.F) ⊗ₜ[D.host.F] Eqv.alphaE D = 0
  rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]

theorem thC_emb (y : D.what₂.Tau → ℂ) (ρ : D.what₂.Tau) : Eqv.thetaC D ρ (infPart D (emb y)) = y ρ := by
  rw [infPart_emb, Eqv.thetaC_splitInv]

theorem emb_add (y y' : D.what₂.Tau → ℂ) : emb (y + y') = emb y + emb y' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_parts D
  · rw [map_sub, map_add, infPart_emb, infPart_emb, infPart_emb, ← Eqv.splitEquiv_symm, map_add, sub_self]
  · rw [map_sub, map_add, finPart_emb, finPart_emb, finPart_emb, add_zero, sub_self]

theorem emb_zero : emb (0 : D.what₂.Tau → ℂ) = 0 := by
  simpa using emb_add (D := D) 0 0

theorem continuous_emb : Continuous (emb (D := D)) := by
  have e : (emb (D := D)) = fun y => pairA D.host.F (Eqv.preA D y 0) 0 • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) +
      pairA D.host.F (Eqv.preA D y 1) 0 • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Eqv.alphaE D) := by
    funext y; simp only [emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  have hp : ∀ k, Continuous fun y : D.what₂.Tau → ℂ => pairA D.host.F (Eqv.preA D y k) 0 := by
    intro k
    unfold pairA
    exact (Eqv.continuous_preA D k).prodMk continuous_const
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) _
  have c1 : Continuous fun _ : D.what₂.Tau → ℂ => ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) := continuous_const
  have c2 : Continuous fun _ : D.what₂.Tau → ℂ => ((1 : AF D.host.F) ⊗ₜ[D.host.F] Eqv.alphaE D : AE D) := continuous_const
  exact ((hp 0).smul c1).add ((hp 1).smul c2)

def Lb (D : D7) (m n : ℕ) : V D m n →+ Mx D m n where
  toFun u := Matrix.of fun i j => emb fun ρ => u ρ i j
  map_zero' := by
    ext i j
    exact emb_zero
  map_add' u u' := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    rw [← emb_add]
    rfl

theorem Lb_apply (u : V D m n) (i : Fin m) (j : Fin n) : Lb D m n u i j = emb fun ρ => u ρ i j := rfl

theorem finPart_Lb (u : V D m n) (i : Fin m) (j : Fin n) : finPart D (Lb D m n u i j) = 0 := by
  rw [Lb_apply]
  exact finPart_emb _

theorem compAt_Lb (u : V D m n) (ρ : D.what₂.Tau) : compAt (Eqv.thetaC D) ρ (Lb D m n u) = Matrix.of (u ρ) := by
  ext i j
  simp [compAt, Lb_apply, thC_emb]

theorem continuous_Lb : Continuous (Lb D m n) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun u : V D m n => emb (D := D) fun ρ => u ρ i j
  exact continuous_emb.comp (by fun_prop)

def sigH (D : D7) (m n : ℕ) : Mx D m n →+ V D m n where
  toFun c ρ i j := Eqv.thetaC D ρ (infPart D (c i j))
  map_zero' := by
    funext ρ i j
    show Eqv.thetaC D ρ (infPart D 0) = 0
    rw [(infPart D).map_zero, (Eqv.thetaC D ρ).map_zero]
  map_add' c c' := by
    funext ρ i j
    show Eqv.thetaC D ρ (infPart D (c i j + c' i j)) = _
    rw [(infPart D).map_add, (Eqv.thetaC D ρ).map_add]
    rfl

theorem sigH_apply (c : Mx D m n) (ρ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    sigH D m n c ρ i j = Eqv.thetaC D ρ (infPart D (c i j)) := rfl

theorem continuous_sigH : Continuous (sigH D m n) := by
  refine continuous_pi fun ρ => continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_thC D ρ).comp (continuous_id.matrix_elem i j)

theorem infPart_Lb_sigH (c : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D (Lb D m n (sigH D m n c) i j) = infPart D (c i j) := by
  rw [Lb_apply, infPart_emb, ← Eqv.splitEquiv_symm, RingEquiv.symm_apply_eq]
  funext ρ
  rw [Eqv.splitEquiv_apply, sigH_apply]

theorem Lb_sigH (c : Mx D m n) (h : ∀ i j, finPart D (c i j) = 0) : Lb D m n (sigH D m n c) = c := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts D
  · rw [map_sub, infPart_Lb_sigH, sub_self]
  · rw [map_sub, finPart_Lb, h, sub_self]

open Classical in

def sg (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : V D m n := fun ρ i j => if ρ = τ then z i j else 0

theorem line_eq (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (L : ℝ →+ Mx D m n)
    (hL : IsLineAt (Eqv.thetaC D) τ z L) (t : ℝ) : L t = Lb D m n (t • sg τ z) := by
  have hfin : ∀ i j, finPart D (L t i j) = 0 := fun i j => by
    have := congrFun (congrFun (hL.2.1 t) i) j
    rw [Matrix.map_apply, Matrix.zero_apply] at this
    exact this
  rw [← Lb_sigH (L t) hfin]
  congr 1
  funext ρ i j
  have h2 := congrFun (congrFun (hL.2.2 t ρ) i) j
  rw [sigH_apply, show Eqv.thetaC D ρ (infPart D (L t i j)) = compAt (Eqv.thetaC D) ρ (L t) i j from rfl, h2]
  simp only [Pi.smul_apply, sg]
  split_ifs <;> simp [Complex.real_smul]

theorem isLineAt_lineAt (hLine : LineAtExists D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt (Eqv.thetaC D) τ z (lineAt (Eqv.thetaC D) τ z) :=
  Classical.epsilon_spec (hLine (Eqv.thetaC D) (Eqv.isInfFam_thetaC D) m n τ z)

theorem lineAt_eq (hLine : LineAtExists D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt (Eqv.thetaC D) τ z t = Lb D m n (t • sg τ z) :=
  line_eq τ z _ (isLineAt_lineAt hLine τ z) t

theorem sg_add (τ : D.what₂.Tau) (z w : Matrix (Fin m) (Fin n) ℂ) : sg τ (z + w) = sg (D := D) τ z + sg τ w := by
  funext ρ i j
  by_cases h : ρ = τ <;> simp [sg, h]

theorem sg_smul (τ : D.what₂.Tau) (r : ℝ) (z : Matrix (Fin m) (Fin n) ℂ) : sg τ ((r : ℂ) • z) = r • sg (D := D) τ z := by
  funext ρ i j
  by_cases h : ρ = τ <;> simp [sg, h]

end Chart

section EM

variable {m n : ℕ} (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ)

theorem eM_add_left (x x' w : Matrix (Fin m) (Fin n) ℂ) : eM GS GT ξ (x + x') w = eM GS GT ξ x w + eM GS GT ξ x' w := by
  simp only [eM, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem eM_add_right (x w w' : Matrix (Fin m) (Fin n) ℂ) : eM GS GT ξ x (w + w') = eM GS GT ξ x w + eM GS GT ξ x w' := by
  simp only [eM, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.add_re]

theorem eM_smul_right (r : ℝ) (x w : Matrix (Fin m) (Fin n) ℂ) : eM GS GT ξ x ((r : ℂ) • w) = r * eM GS GT ξ x w := by
  have hr : star (r : ℂ) = (r : ℂ) := by rw [← starRingEnd_apply, Complex.conj_ofReal]
  simp only [eM, Matrix.conjTranspose_smul, hr, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem eM_zero_left (w : Matrix (Fin m) (Fin n) ℂ) : eM GS GT ξ 0 w = 0 := by
  simp [eM]

theorem eM_zero_right (x : Matrix (Fin m) (Fin n) ℂ) : eM GS GT ξ x 0 = 0 := by
  simp [eM]

theorem eM_swap (hS : GSᴴ = GS) (hT : GTᴴ = GT) (hξ : starRingEnd ℂ ξ = -ξ) (x w : Matrix (Fin m) (Fin n) ℂ) :
    eM GS GT ξ w x = -eM GS GT ξ x w := by
  have key : (GS⁻¹ * xᴴ * GT * w).trace = star (GS⁻¹ * wᴴ * GT * x).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hT, Matrix.conjTranspose_nonsing_inv, hS,
      show xᴴ * (GT * (w * GS⁻¹)) = (xᴴ * GT * w) * GS⁻¹ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm (xᴴ * GT * w)]
    simp only [Matrix.mul_assoc]
  have h1 : ξ.re = 0 := by
    have := congrArg Complex.re hξ
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  unfold eM
  rw [key, ← starRingEnd_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, h1]
  ring

theorem continuous_eM_left (w : Matrix (Fin m) (Fin n) ℂ) : Continuous fun z : Matrix (Fin m) (Fin n) ℂ => eM GS GT ξ z w := by
  unfold eM
  exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul
    (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))))

end EM

section Phase

variable (S T : HSp D)

def eR (ρ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  eM (gramAt D S ρ) (gramAt D T ρ) (tauE D ρ D.host.xi0) x y

def phR (a : WO S T) (u : V D T.rank S.rank) : ℝ :=
  ∑ ρ, eR S T ρ (compAt (Eqv.thetaC D) ρ a) (Matrix.of (u ρ))

theorem gramAt_herm (W : HSp D) (ρ : D.what₂.Tau) : (gramAt D W ρ)ᴴ = gramAt D W ρ := by
  ext i j
  rw [Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Matrix.map_apply,
    show star (tauE D ρ (W.gram j i)) = tauE D ρ (star (W.gram j i)) from (Eqv.tauE_star D ρ _).symm,
    ← Matrix.conjTranspose_apply, Brg.gram_herm]

theorem conj_purely_imaginary_generator (ρ : D.what₂.Tau) : starRingEnd ℂ (tauE D ρ D.host.xi0) = -tauE D ρ D.host.xi0 := by
  rw [← Eqv.tauE_star, Brg.star_purely_imaginary_eq_neg, map_neg]

theorem eR_swap (ρ : D.what₂.Tau) (x w : Matrix (Fin T.rank) (Fin S.rank) ℂ) : eR S T ρ w x = -eR S T ρ x w := eM_swap _ _ _ (gramAt_herm S ρ) (gramAt_herm T ρ) (conj_purely_imaginary_generator ρ) x w

theorem compAt_add {m n : ℕ} (ρ : D.what₂.Tau) (a a' : Mx D m n) :
    compAt (Eqv.thetaC D) ρ (a + a') = compAt (Eqv.thetaC D) ρ a + compAt (Eqv.thetaC D) ρ a' := by
  ext i j
  simp [compAt, map_add]

theorem phR_add_left (a a' : WO S T) (u : V D T.rank S.rank) : phR S T (a + a') u = phR S T a u + phR S T a' u := by
  unfold phR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [compAt_add]
  exact eM_add_left _ _ _ _ _ _

theorem phR_add_right (a : WO S T) (u u' : V D T.rank S.rank) : phR S T a (u + u') = phR S T a u + phR S T a u' := by
  unfold phR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Pi.add_apply, ← Matrix.of_add_of]
  exact eM_add_right _ _ _ _ _ _

theorem phR_smul (a : WO S T) (r : ℝ) (u : V D T.rank S.rank) : phR S T a (r • u) = r * phR S T a u := by
  unfold phR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hm : Matrix.of ((r • u) ρ) = (r : ℂ) • Matrix.of (u ρ) := by
    ext i j
    simp [Complex.real_smul]
  rw [hm]
  exact eM_smul_right _ _ _ _ _ _

theorem phR_sg (a : WO S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    phR S T a (sg τ z) = eR S T τ (compAt (Eqv.thetaC D) τ a) z := by
  unfold phR
  rw [Finset.sum_eq_single τ]
  · congr 1
    ext i j
    simp [sg]
  · intro ρ _ hρ
    have hz : Matrix.of (sg (D := D) τ z ρ) = 0 := by
      ext i j
      simp [sg, hρ]
    rw [hz]
    exact eM_zero_right _ _ _ _
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem map_inv_gram (W : HSp D) (ρ : D.what₂.Tau) : (W.gram⁻¹).map (tauE D ρ) = (gramAt D W ρ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [gramAt, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne W)),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_hO {R : Type} [CommRing R] (φ : AE D →+* R) (a y : WO S T) :
    φ (hO S T a y) = ((Brg.GI S).map φ * ((y.map (cA D))ᵀ).map φ * (Brg.GG T).map φ * a.map φ).trace := by
  rw [Fin.hO_eq_trace]
  unfold Fin.hOM
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
  unfold Matrix.trace
  exact map_sum φ _ _

theorem thC_hO (ρ : D.what₂.Tau) (a y : WO S T) :
    Eqv.thetaC D ρ (infPart D (hO S T a y)) =
      ((gramAt D S ρ)⁻¹ * (compAt (Eqv.thetaC D) ρ y)ᴴ * gramAt D T ρ * compAt (Eqv.thetaC D) ρ a).trace := by
  let φ : AE D →+* ℂ := (Eqv.thetaC D ρ).comp (infPart D)
  have hφ : ∀ c, Eqv.thetaC D ρ (infPart D c) = φ c := fun _ => rfl
  rw [hφ, map_hO]
  have e1 : (Brg.GI S).map φ = (gramAt D S ρ)⁻¹ := by
    rw [← map_inv_gram]
    show ((S.gram⁻¹).map (incA D)).map φ = _
    rw [Matrix.map_map]
    congr 1
    funext e
    exact thC_incA D ρ e
  have e2 : ((y.map (cA D))ᵀ).map φ = (compAt (Eqv.thetaC D) ρ y)ᴴ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, compAt, ← hφ, thC_cA]
    rfl
  have e3 : (Brg.GG T).map φ = gramAt D T ρ := by
    show ((T.gram).map (incA D)).map φ = _
    rw [Matrix.map_map, gramAt]
    congr 1
    funext e
    exact thC_incA D ρ e
  rw [e1, e2, e3]
  rfl

theorem finPart_cA_eq_zero (c : AE D) (h : finPart D c = 0) : finPart D (cA D c) = 0 := by
  rw [finPart_cA, h, map_zero]

theorem infPart_cA_eq_zero (c : AE D) (h : infPart D c = 0) : infPart D (cA D c) = 0 := by
  rw [infPart_cA, h, map_zero]

theorem finPart_hO (a y : WO S T) (hy : ∀ i j, finPart D (y i j) = 0) : finPart D (hO S T a y) = 0 := by
  have e : ((y.map (cA D))ᵀ).map (finPart D) = 0 := by
    ext i j
    exact finPart_cA_eq_zero _ (hy _ _)
  rw [map_hO, e, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

theorem finPart_hO' (a y : WO S T) (ha : ∀ i j, finPart D (a i j) = 0) : finPart D (hO S T a y) = 0 := by
  have e : a.map (finPart D) = 0 := by
    ext i j
    exact ha _ _
  rw [map_hO, e, Matrix.mul_zero, Matrix.trace_zero]

theorem infPart_hO (a y : WO S T) (hy : ∀ i j, infPart D (y i j) = 0) : infPart D (hO S T a y) = 0 := by
  have e : ((y.map (cA D))ᵀ).map (infPart D) = 0 := by
    ext i j
    exact infPart_cA_eq_zero _ (hy _ _)
  rw [map_hO, e, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

theorem infPart_hO' (a y : WO S T) (ha : ∀ i j, infPart D (a i j) = 0) : infPart D (hO S T a y) = 0 := by
  have e : a.map (infPart D) = 0 := by
    ext i j
    exact ha _ _
  rw [map_hO, e, Matrix.mul_zero, Matrix.trace_zero]

theorem symplOH_real_fin (a b : WO S T) (ha : ∀ i j, finPart D (a i j) = 0) (hb : ∀ i j, infPart D (b i j) = 0) :
    symplOH S T a b = 0 ∧ symplOH S T b a = 0 := by
  have h1 : hO S T a b = 0 := eq_zero_of_parts D _ (infPart_hO S T a b hb) (finPart_hO' S T a b ha)
  have h2 : hO S T b a = 0 := eq_zero_of_parts D _ (infPart_hO' S T b a hb) (finPart_hO S T b a ha)
  unfold symplOH symplO
  rw [h1, h2, mul_zero, map_zero, mul_zero]
  exact ⟨rfl, rfl⟩

theorem symplOH_eq_coord (a y : WO S T) :
    symplOH S T a y = (basR D (AF D.host.F)).repr (incA D D.host.xi0 * hO S T a y) 0 := by
  unfold symplOH symplO
  rw [traceAE, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem psi_real {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a y : WO S T)
    (hy : ∀ i j, finPart D (y i j) = 0) :
    ψ (symplOH S T a y) = Complex.exp (-(Real.pi : ℂ) * Complex.I *
      ((∑ ρ, eR S T ρ (compAt (Eqv.thetaC D) ρ a) (compAt (Eqv.thetaC D) ρ y) : ℝ) : ℂ)) := by
  set w := incA D D.host.xi0 * hO S T a y with hw
  have hfw : finPart D w = 0 := by rw [hw, RingHom.map_mul, finPart_hO S T a y hy, mul_zero]
  rw [symplOH_eq_coord, psi_of_snd D hψ _ (fin_coord_zero D w hfw).1]
  congr 1
  have hρ : ∀ ρ, Eqv.thetaC D ρ (fstA D.host.F ((basR D (AF D.host.F)).repr w 0) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((eR S T ρ (compAt (Eqv.thetaC D) ρ a) (compAt (Eqv.thetaC D) ρ y) / 2 : ℝ) : ℂ) := by
    intro ρ
    rw [Eqv.thetaC_tmul, map_one, mul_one, ← re_thC]
    congr 1
    rw [hw, (infPart D).map_mul, (Eqv.thetaC D ρ).map_mul, thC_incA, thC_hO, eR, eM]
    ring
  rw [Finset.sum_congr rfl fun ρ _ => hρ ρ, ← Complex.ofReal_sum, ← Finset.sum_div]
  push_cast
  ring

theorem psi_Lb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : WO S T) (u : V D T.rank S.rank) :
    ψ (symplOH S T a (Lb D _ _ u)) = Complex.exp (-(Real.pi : ℂ) * Complex.I * (phR S T a u : ℂ)) := by
  rw [psi_real S T hψ a (Lb D _ _ u) (fun i j => finPart_Lb u i j)]
  simp only [compAt_Lb, phR]

end Phase

section Calc

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

def G (f : WO S T → ℂ) (x : WO S T) : V D T.rank S.rank → ℂ := fun u => f (x + Lb D _ _ u)

theorem G_shift (f : WO S T → ℂ) (x : WO S T) (a : V D T.rank S.rank) :
    G f (x + Lb D _ _ a) = fun u => G f x (a + u) := by
  funext u
  show f (x + Lb D _ _ a + Lb D _ _ u) = f (x + Lb D _ _ (a + u))
  rw [map_add, add_assoc]

theorem contDiff_G {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) : ContDiff ℝ ∞ (G f x) := by
  let b := Module.finBasis ℝ (V D T.rank S.rank)
  let φ : (Fin (Module.finrank ℝ (V D T.rank S.rank)) → ℝ) →ₗ[ℝ] V D T.rank S.rank := b.equivFun.symm.toLinearMap
  let L' : (Fin (Module.finrank ℝ (V D T.rank S.rank)) → ℝ) →+ WO S T := (Lb D _ _).comp φ.toAddMonoidHom
  have hc : Continuous L' := continuous_Lb.comp (LinearMap.continuous_of_finiteDimensional φ)
  have h := hf.smooth _ L' hc (fun t => by ext i j; exact finPart_Lb _ i j) x
  let ψ' : V D T.rank S.rank →L[ℝ] (Fin (Module.finrank ℝ (V D T.rank S.rank)) → ℝ) :=
    LinearMap.toContinuousLinearMap b.equivFun.toLinearMap
  have e : G f x = (fun s => f (x + L' s)) ∘ ψ' := by
    funext u
    show f (x + Lb D _ _ u) = f (x + Lb D _ _ (b.equivFun.symm (b.equivFun u)))
    rw [LinearEquiv.symm_apply_apply]
  rw [e]
  exact h.comp ψ'.contDiff

theorem hasFDerivAt_G {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) (u : V D T.rank S.rank) :
    HasFDerivAt (G f x) (fderiv ℝ (G f x) u) u :=
  ((contDiff_G hf x).differentiable (by simp)).differentiableAt.hasFDerivAt

theorem heis_Lb (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (x : WO S T) (u : V D T.rank S.rank) :
    heisO ψ S T (Lb D _ _ u) f x = Complex.exp (-(Real.pi : ℂ) * Complex.I * (phR S T x u : ℂ)) * G f x u := by
  show ψ (symplOH S T x (Lb D _ _ u)) * f (x + Lb D _ _ u) = _
  rw [psi_Lb S T hψ x u]
  rfl

theorem hasDerivAt_heis (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (x : WO S T) (hd : DifferentiableAt ℝ (G f x) 0)
    (v : V D T.rank S.rank) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (Lb D _ _ (t • v)) f x)
      (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ) * f x + fderiv ℝ (G f x) 0 v) 0 := by
  have e : (fun t : ℝ => heisO ψ S T (Lb D _ _ (t • v)) f x) = fun t : ℝ =>
      Complex.exp ((t : ℂ) * (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ))) * G f x (t • v) := by
    funext t
    rw [heis_Lb hψ, phR_smul]
    congr 2
    push_cast
    ring
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ))))
      (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ)) 0 := by
    have h := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ))).cexp).comp_ofReal
    simpa using h
  have h2 : HasDerivAt (fun t : ℝ => G f x (t • v)) (fderiv ℝ (G f x) 0 v) 0 := by
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hG : HasFDerivAt (G f x) (fderiv ℝ (G f x) 0) ((fun t : ℝ => t • v) 0) := by
      simp only [zero_smul]
      exact hd.hasFDerivAt
    exact hG.comp_hasDerivAt (0 : ℝ) hl
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-(Real.pi : ℂ) * Complex.I * (phR S T x v : ℂ))) *
      G f x (t • v)) _ 0 := h1.mul h2
  have e0 : G f x ((0 : ℝ) • v) = f x := by
    rw [zero_smul]
    show f (x + Lb D _ _ 0) = f x
    rw [map_zero, add_zero]
  rw [e0] at h3
  simpa using h3

theorem dRho_eq (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (x : WO S T) (hd : DifferentiableAt ℝ (G f x) 0) :
    dRho (heisO ψ S T) (Eqv.thetaC D) τ z f x =
      -(Real.pi : ℂ) * Complex.I * (phR S T x (sg τ z) : ℂ) * f x + fderiv ℝ (G f x) 0 (sg τ z) := by
  show deriv (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f x) 0 = _
  simp only [lineAt_eq hLine]
  exact (hasDerivAt_heis hψ x hd _).deriv

theorem hasDerivAt_dRho (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (x : WO S T) (hd : DifferentiableAt ℝ (G f x) 0) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f x)
      (dRho (heisO ψ S T) (Eqv.thetaC D) τ z f x) 0 := by
  rw [dRho_eq hψ hLine τ z x hd]
  simp only [lineAt_eq hLine]
  exact hasDerivAt_heis hψ x hd _

theorem cont_cA : Continuous (cA D) := by
  let l : AE D →ₗ[AF D.host.F] AE D :=
    { toFun := cA D, map_add' := (cA D).map_add, map_smul' := Formalism.IndefR.PHeisTh.cA_smul }
  exact IsModuleTopology.continuous_of_linearMap l

theorem cont_symplOH_right (S T : HSp D) (x : WO S T) : Continuous fun y : WO S T => symplOH S T x y := by
  have hh : Continuous fun y : WO S T => hO S T x y := by
    unfold hO
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
    refine (((continuous_const.mul ?_).mul continuous_const).mul continuous_const)
    exact cont_cA.comp ((continuous_apply b).comp (continuous_apply c))
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOH symplO
  exact continuous_const.mul (htr.comp (continuous_const.mul hh))

theorem continuous_compAt {m n : ℕ} (ρ : D.what₂.Tau) : Continuous fun x : Mx D m n => compAt (Eqv.thetaC D) ρ x := by
  refine continuous_matrix fun i j => ?_
  simp only [compAt, Matrix.of_apply, Matrix.map_apply]
  exact (continuous_thC D ρ).comp (continuous_id.matrix_elem i j)

theorem continuous_phR (v : V D T.rank S.rank) : Continuous fun x : WO S T => phR S T x v := by
  unfold phR
  exact continuous_finset_sum _ fun ρ _ => (continuous_eM_left _ _ _ _).comp (continuous_compAt ρ)

variable (S T) in

def lH (v : V D T.rank S.rank) : V D T.rank S.rank →+ ℝ where
  toFun u := phR S T (Lb D _ _ u) v
  map_zero' := by
    rw [map_zero]
    have h := phR_add_left S T 0 0 v
    rw [add_zero] at h
    linarith
  map_add' u u' := by
    rw [map_add, phR_add_left]

variable (S T) in

def lCL (v : V D T.rank S.rank) : V D T.rank S.rank →L[ℝ] ℝ :=
  (lH S T v).toRealLinearMap ((continuous_phR v).comp continuous_Lb)

theorem lCL_apply (v u : V D T.rank S.rank) : lCL S T v u = phR S T (Lb D _ _ u) v := rfl

theorem continuous_DG (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : V D T.rank S.rank) :
    Continuous fun x : WO S T => fderiv ℝ (G f x) 0 v := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  rw [continuous_iff_continuousAt]
  intro x0
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  let sg0 : WO S T → V D T.rank S.rank := fun x => sigH D _ _ (x - x0)
  let b : WO S T → WO S T := fun x => x + Lb D _ _ (-(sg0 x)) + -x0
  have hsc : Continuous sg0 := by
    have e : sg0 = fun x => sigH D _ _ x - sigH D _ _ x0 := funext fun x => map_sub _ _ _
    rw [e]
    exact continuous_sigH.sub continuous_const
  have hb : Continuous b := (continuous_id.add (continuous_Lb.comp hsc.neg)).add continuous_const
  have hb0 : b x0 = 0 := by simp [b, sg0]
  have hbinf : ∀ x i j, infPart D (b x i j) = 0 := by
    intro x i j
    have e : b x = x - x0 - Lb D _ _ (sigH D _ _ (x - x0)) := by
      simp only [b, sg0, map_neg]
      abel
    rw [e]
    show infPart D ((x - x0) i j - Lb D _ _ (sigH D _ _ (x - x0)) i j) = 0
    rw [(infPart D).map_sub, infPart_Lb_sigH, sub_self]
  have hψ0 : ∀ a, ψ a ≠ 0 := fun a h => by
    have := hψ.1.2.1 a
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have key : ∀ x, b x ∈ U →
      fderiv ℝ (G f x) 0 v = (ψ (symplOH S T x0 (b x)))⁻¹ * fderiv ℝ (G f x0) (sg0 x) v := by
    intro x hx
    have hGx : G f x = fun u => (ψ (symplOH S T x0 (b x)))⁻¹ * G f x0 (sg0 x + u) := by
      funext u
      have hx' : x + Lb D _ _ u = x0 + Lb D _ _ (sg0 x + u) + b x := by
        simp only [b, map_add, map_neg]
        abel
      have hl := congrFun (hU (b x) hx (by ext i j; exact hbinf x i j)) (x0 + Lb D _ _ (sg0 x + u))
      have h0 := (symplOH_real_fin S T (Lb D _ _ (sg0 x + u)) (b x) (finPart_Lb _) (hbinf x)).1
      change ψ (symplOH S T (x0 + Lb D _ _ (sg0 x + u)) (b x)) * f (x0 + Lb D _ _ (sg0 x + u) + b x) =
        f (x0 + Lb D _ _ (sg0 x + u)) at hl
      rw [Fin.symplOH_add_left, h0, add_zero] at hl
      show f (x + Lb D _ _ u) = (ψ (symplOH S T x0 (b x)))⁻¹ * f (x0 + Lb D _ _ (sg0 x + u))
      rw [hx', ← hl, ← mul_assoc, inv_mul_cancel₀ (hψ0 _), one_mul]
    rw [hGx]
    have hc : HasFDerivAt (fun u => (ψ (symplOH S T x0 (b x)))⁻¹ * G f x0 (sg0 x + u))
        ((ψ (symplOH S T x0 (b x)))⁻¹ • fderiv ℝ (G f x0) (sg0 x)) 0 := by
      have hd : HasFDerivAt (G f x0) (fderiv ℝ (G f x0) (sg0 x)) ((fun u : V D T.rank S.rank => sg0 x + u) 0) := by
        simp only [add_zero]
        exact hasFDerivAt_G hf x0 _
      have := (hd.comp (0 : V D T.rank S.rank) ((hasFDerivAt_id (0 : V D T.rank S.rank)).const_add (sg0 x))).const_mul
        (ψ (symplOH S T x0 (b x)))⁻¹
      simpa [Function.comp_def] using this
    rw [hc.fderiv]
    simp
  have hcont : Continuous fun x => (ψ (symplOH S T x0 (b x)))⁻¹ * fderiv ℝ (G f x0) (sg0 x) v := by
    refine Continuous.mul ?_ ?_
    · exact (hψ.1.1.comp ((cont_symplOH_right S T x0).comp hb)).inv₀ fun x => hψ0 _
    · exact (((contDiff_G hf x0).continuous_fderiv (by simp)).comp hsc).clm_apply continuous_const
  have hev : ∀ᶠ x in nhds x0, b x ∈ U :=
    hb.continuousAt.preimage_mem_nhds (by rw [hb0]; exact hUo.mem_nhds U.zero_mem)
  exact hcont.continuousAt.congr (hev.mono fun x hx => (key x hx).symm)

theorem heis_quasi {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w₀ : WO S T)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    heisO ψ S T w₀ f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * heisO ψ S T w₀ f w := by
  show ψ (symplOH S T (ratW T S γ + w) w₀) * f (ratW T S γ + w + w₀) =
    ψ (-(symplOH S T (ratW T S γ) w)) * (ψ (symplOH S T w w₀) * f (w + w₀))
  rw [add_assoc, hf.quasi, Fin.symplOH_add_left, Fin.symplOH_add_right, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  abel

theorem dRho_quasi (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    dRho (heisO ψ S T) (Eqv.thetaC D) τ z f (ratW T S γ + w) =
      ψ (-(symplOH S T (ratW T S γ) w)) * dRho (heisO ψ S T) (Eqv.thetaC D) τ z f w := by
  have e : (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f (ratW T S γ + w)) =
      fun t => ψ (-(symplOH S T (ratW T S γ) w)) * heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f w := by
    funext t
    exact heis_quasi hf _ γ w
  show deriv _ 0 = _
  rw [e]
  exact ((hasDerivAt_dRho hψ hLine τ z w (hasFDerivAt_G hf w 0).differentiableAt).const_mul _).deriv

theorem dRho_level (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T)
    (hu : heisO ψ S T u f = f) (hinf : ∀ i j, infPart D (u i j) = 0) :
    heisO ψ S T u (dRho (heisO ψ S T) (Eqv.thetaC D) τ z f) = dRho (heisO ψ S T) (Eqv.thetaC D) τ z f := by
  funext x
  have key : ∀ t : ℝ, heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f x =
      ψ (symplOH S T x u) * heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f (x + u) := by
    intro t
    rw [lineAt_eq hLine]
    obtain ⟨h1, h2⟩ := symplOH_real_fin S T (Lb D _ _ (t • sg τ z)) u (finPart_Lb _) hinf
    have hf' := congrFun hu (x + Lb D _ _ (t • sg τ z))
    show ψ (symplOH S T x (Lb D _ _ (t • sg τ z))) * f (x + Lb D _ _ (t • sg τ z)) =
      ψ (symplOH S T x u) * (ψ (symplOH S T (x + u) (Lb D _ _ (t • sg τ z))) * f (x + u + Lb D _ _ (t • sg τ z)))
    rw [← hf']
    show ψ (symplOH S T x (Lb D _ _ (t • sg τ z))) *
      (ψ (symplOH S T (x + Lb D _ _ (t • sg τ z)) u) * f (x + Lb D _ _ (t • sg τ z) + u)) = _
    rw [Fin.symplOH_add_left, Fin.symplOH_add_left, h1, h2, add_zero, add_zero, add_right_comm]
    ring
  show ψ (symplOH S T x u) * deriv _ 0 = deriv _ 0
  rw [show (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f x) =
    fun t => ψ (symplOH S T x u) * heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) f (x + u) from funext key]
  exact (((hasDerivAt_dRho hψ hLine τ z (x + u) (hasFDerivAt_G hf _ 0).differentiableAt).const_mul _).deriv).symm

theorem dRho_chart (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T)
    (a : V D T.rank S.rank) :
    dRho (heisO ψ S T) (Eqv.thetaC D) τ z f (w + Lb D _ _ a) =
      -(Real.pi : ℂ) * Complex.I * ((phR S T w (sg τ z) + lCL S T (sg τ z) a : ℝ) : ℂ) * G f w a +
        fderiv ℝ (G f w) a (sg τ z) := by
  rw [dRho_eq hψ hLine τ z _ (hasFDerivAt_G hf _ 0).differentiableAt, phR_add_left, lCL_apply]
  congr 1
  rw [G_shift]
  have hd : HasFDerivAt (G f w) (fderiv ℝ (G f w) a) ((fun u : V D T.rank S.rank => a + u) 0) := by
    simp only [add_zero]
    exact hasFDerivAt_G hf w _
  have hc : HasFDerivAt (fun u => G f w (a + u)) (fderiv ℝ (G f w) a) 0 := by
    have := hd.comp (0 : V D T.rank S.rank) ((hasFDerivAt_id (0 : V D T.rank S.rank)).const_add a)
    simpa [Function.comp_def] using this
  rw [hc.fderiv]

theorem contDiff_dRho_chart (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    ContDiff ℝ ∞ fun a : V D T.rank S.rank => dRho (heisO ψ S T) (Eqv.thetaC D) τ z f (w + Lb D _ _ a) := by
  simp only [dRho_chart hψ hLine τ z hf w]
  have h1 : ContDiff ℝ ∞ fun a : V D T.rank S.rank => ((phR S T w (sg τ z) + lCL S T (sg τ z) a : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.add (lCL S T (sg τ z)).contDiff)
  have h2 : ContDiff ℝ ∞ fun a => fderiv ℝ (G f w) a (sg τ z) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_G hf w)).2.clm_apply contDiff_const
  exact ((contDiff_const.mul h1).mul (contDiff_G hf w)).add h2

theorem theta_dRho (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (dRho (heisO ψ S T) (Eqv.thetaC D) τ z f) where
  quasi γ w := dRho_quasi hψ hLine τ z hf γ w
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hinf => dRho_level hψ hLine τ z hf u (hU u hu hinf) fun i j => ?_⟩
    have := congrFun (congrFun hinf i) j
    rw [Matrix.map_apply, Matrix.zero_apply] at this
    exact this
  cont := by
    have e : dRho (heisO ψ S T) (Eqv.thetaC D) τ z f = fun x =>
        -(Real.pi : ℂ) * Complex.I * (phR S T x (sg τ z) : ℂ) * f x + fderiv ℝ (G f x) 0 (sg τ z) := by
      funext x
      exact dRho_eq hψ hLine τ z x (hasFDerivAt_G hf x 0).differentiableAt
    rw [e]
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_phR _))).mul hf.cont).add
      (continuous_DG hψ hf _)
  smooth := by
    intro k L hL hfin w
    let A : (Fin k → ℝ) →+ V D T.rank S.rank := (sigH D _ _).comp L
    have hA : Continuous A := continuous_sigH.comp hL
    let A' := A.toRealLinearMap hA
    have e : (fun t => dRho (heisO ψ S T) (Eqv.thetaC D) τ z f (w + L t)) =
        (fun a => dRho (heisO ψ S T) (Eqv.thetaC D) τ z f (w + Lb D _ _ a)) ∘ A' := by
      funext t
      simp only [Function.comp_apply]
      congr 2
      refine (Lb_sigH (L t) fun i j => ?_).symm
      have := congrFun (congrFun (hfin t) i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    rw [e]
    exact (contDiff_dRho_chart hψ hLine τ z hf w).comp A'.contDiff

theorem fderiv_G_dRho (hψ : IsStdChar D ψ (-1)) (hLine : LineAtExists D) (τ' : D.what₂.Tau)
    (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T)
    (v : V D T.rank S.rank) :
    fderiv ℝ (G (dRho (heisO ψ S T) (Eqv.thetaC D) τ' w f) x) 0 v =
      -(Real.pi : ℂ) * Complex.I * (lCL S T (sg τ' w) v : ℂ) * f x +
        -(Real.pi : ℂ) * Complex.I * (phR S T x (sg τ' w) : ℂ) * fderiv ℝ (G f x) 0 v +
        fderiv ℝ (fderiv ℝ (G f x)) 0 v (sg τ' w) := by
  have hGg : G (dRho (heisO ψ S T) (Eqv.thetaC D) τ' w f) x = fun u =>
      -(Real.pi : ℂ) * Complex.I * ((phR S T x (sg τ' w) + lCL S T (sg τ' w) u : ℝ) : ℂ) * G f x u +
        fderiv ℝ (G f x) u (sg τ' w) := by
    funext u
    exact dRho_chart hψ hLine τ' w hf x u
  rw [hGg]
  have hG0 : HasFDerivAt (G f x) (fderiv ℝ (G f x) 0) 0 := hasFDerivAt_G hf x 0
  have hl : HasFDerivAt
      (fun u : V D T.rank S.rank => -(Real.pi : ℂ) * Complex.I * ((phR S T x (sg τ' w) + lCL S T (sg τ' w) u : ℝ) : ℂ))
      ((-(Real.pi : ℂ) * Complex.I) • (Complex.ofRealCLM.comp (lCL S T (sg τ' w)))) 0 := by
    have h1 : HasFDerivAt (fun u => phR S T x (sg τ' w) + lCL S T (sg τ' w) u) (lCL S T (sg τ' w)) 0 :=
      (lCL S T (sg τ' w)).hasFDerivAt.const_add _
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp (0 : V D T.rank S.rank) h1).const_mul (-(Real.pi : ℂ) * Complex.I)
    simpa [Function.comp_def] using h2
  have hd2 : HasFDerivAt (fderiv ℝ (G f x)) (fderiv ℝ (fderiv ℝ (G f x)) 0) 0 :=
    (((contDiff_infty_iff_fderiv.1 (contDiff_G hf x)).2.differentiable (by simp)) 0).hasFDerivAt
  have h3 : HasFDerivAt (fun u => fderiv ℝ (G f x) u (sg τ' w)) ((fderiv ℝ (fderiv ℝ (G f x)) 0).flip (sg τ' w)) 0 := by
    have := hd2.clm_apply (hasFDerivAt_const (sg (D := D) τ' w) (0 : V D T.rank S.rank))
    simpa using this
  have hall : HasFDerivAt (fun u : V D T.rank S.rank =>
      -(Real.pi : ℂ) * Complex.I * ((phR S T x (sg τ' w) + lCL S T (sg τ' w) u : ℝ) : ℂ) * G f x u +
        fderiv ℝ (G f x) u (sg τ' w)) _ 0 := (hl.mul hG0).add h3
  rw [hall.fderiv]
  simp [G]
  ring

open Classical in
theorem lCL_sg (τ τ' : D.what₂.Tau) (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    lCL S T (sg τ' w) (sg τ z) = if τ = τ' then eR S T τ z w else 0 := by
  rw [lCL_apply, phR_sg, compAt_Lb]
  by_cases h : τ = τ'
  · subst h
    rw [if_pos rfl]
    congr 1
    ext i j
    simp [sg]
  · rw [if_neg h]
    have hz : Matrix.of (sg (D := D) τ z τ') = 0 := by
      ext i j
      simp [sg, Ne.symm h]
    rw [hz]
    exact eM_zero_left _ _ _ _

end Calc

theorem thetaDRho (D : D7) : ThetaDRho D := by
  intro ψ θ hψ hθ hLine S T τ z f hf
  obtain rfl := Eqv.eq_thetaC D hθ
  exact ⟨theta_dRho hψ hLine τ z hf, fun x => hasDerivAt_dRho hψ hLine τ z x (hasFDerivAt_G hf x 0).differentiableAt⟩

theorem dRhoLin (D : D7) : DRhoLin D := by
  intro ψ θ hψ hθ hLine S T τ
  obtain rfl := Eqv.eq_thetaC D hθ
  have hdf : ∀ {f : WO S T → ℂ}, IsThetaFunO ψ S T f → ∀ x, DifferentiableAt ℝ (G f x) 0 :=
    fun hf x => (hasFDerivAt_G hf x 0).differentiableAt
  refine ⟨fun z w f hf => ?_, fun r z f hf => ?_, fun z c f g hf hg => ?_⟩
  · funext x
    simp only [Pi.add_apply]
    rw [dRho_eq hψ hLine τ _ x (hdf hf x), dRho_eq hψ hLine τ _ x (hdf hf x), dRho_eq hψ hLine τ _ x (hdf hf x),
      sg_add, phR_add_right, map_add]
    push_cast
    ring
  · funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [dRho_eq hψ hLine τ _ x (hdf hf x), dRho_eq hψ hLine τ _ x (hdf hf x), sg_smul, phR_smul, map_smul,
      Complex.real_smul]
    push_cast
    ring
  · funext x
    have hG : G (f + c • g) x = G f x + c • G g x := rfl
    have hdg : DifferentiableAt ℝ (G (f + c • g) x) 0 := by
      rw [hG]
      exact (hdf hf x).add ((hdf hg x).const_smul c)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [dRho_eq hψ hLine τ z x hdg, dRho_eq hψ hLine τ z x (hdf hf x), dRho_eq hψ hLine τ z x (hdf hg x), hG,
      fderiv_add (hdf hf x) ((hdf hg x).const_smul c), fderiv_const_smul (hdf hg x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    ring

theorem dRhoComm (D : D7) : DRhoComm D := by
  intro ψ θ hψ hθ hLine S T τ τ' z w f hf
  obtain rfl := Eqv.eq_thetaC D hθ
  have hg1 := theta_dRho hψ hLine τ' w hf
  have hg2 := theta_dRho hψ hLine τ z hf
  funext x
  have hsym : IsSymmSndFDerivAt ℝ (G f x) 0 := (contDiff_G hf x).contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top)
  rw [Pi.sub_apply, dRho_eq hψ hLine τ z x (hasFDerivAt_G hg1 x 0).differentiableAt,
    dRho_eq hψ hLine τ' w x (hasFDerivAt_G hg2 x 0).differentiableAt,
    fderiv_G_dRho hψ hLine τ' w hf x, fderiv_G_dRho hψ hLine τ z hf x,
    dRho_eq hψ hLine τ' w x (hasFDerivAt_G hf x 0).differentiableAt,
    dRho_eq hψ hLine τ z x (hasFDerivAt_G hf x 0).differentiableAt,
    hsym (sg τ' w) (sg τ z), lCL_sg, lCL_sg]
  by_cases h : τ = τ'
  · subst h
    rw [if_pos rfl, if_pos rfl, if_pos rfl, eR_swap S T τ z w, Pi.smul_apply, smul_eq_mul, eR]
    push_cast
    ring
  · rw [if_neg h, if_neg (Ne.symm h), if_neg h, Pi.zero_apply]
    push_cast
    ring

end Formalism.IndefR.Fock.DRho

end
