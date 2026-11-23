import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Single

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst) (p : HeightOneSpectrum (𝓞 I.F))

abbrev eP : Af I.F ⊗[I.F] I.E := chi I p ⊗ₜ[I.F] (1 : I.E)

theorem HelpSng_sL_mul (a b : Fv I.F p) : sL I p (a * b) = sL I p a * sL I p b := by
  show singleV I.F p (a * b) = singleV I.F p a * singleV I.F p b
  apply FiniteAdeleRing.ext; intro v
  rw [Comp_mul_apply]
  by_cases h : v = p
  · subst h; simp only [Comp_single_same]
  · simp only [Comp_single_ne I p v h, mul_zero]

private theorem localTheta_tmul (a : Fv I.F p) (b : I.E) :
    thetaP I p (a ⊗ₜ[I.F] b) = sL I p a ⊗ₜ[I.F] b := rfl

theorem HelpSng_theta_mul (x y : Fv I.F p ⊗[I.F] I.E) :
    thetaP I p (x * y) = thetaP I p x * thetaP I p y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, localTheta_tmul, localTheta_tmul, localTheta_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, HelpSng_sL_mul]
    | add y1 y2 h1 h2 => simp only [mul_add, map_add, h1, h2]
  | add x1 x2 h1 h2 => simp only [add_mul, map_add, h1, h2]

theorem HelpSng_theta_one : thetaP I p 1 = eP I p := by
  rw [Algebra.TensorProduct.one_def, localTheta_tmul]
  rfl

theorem HelpSng_theta_inclR (x : I.E) :
    thetaP I p (inclR (Fv I.F p) x) = eP I p * inclR (Af I.F) x := by
  have h1 : inclR (Fv I.F p) x = (1 : Fv I.F p) ⊗ₜ[I.F] x := rfl
  have h2 : inclR (Af I.F) x = (1 : Af I.F) ⊗ₜ[I.F] x := rfl
  rw [h1, h2, localTheta_tmul]
  show sL I p 1 ⊗ₜ[I.F] x = (chi I p ⊗ₜ[I.F] (1 : I.E)) * ((1 : Af I.F) ⊗ₜ[I.F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

private theorem tensMap_tmul_lemma_2 (v : HeightOneSpectrum (𝓞 I.F)) (a : Af I.F) (b : I.E) :
    tensMap (E := I.E) (evalV I.F v) (a ⊗ₜ[I.F] b) = evalV I.F v a ⊗ₜ[I.F] b := rfl

theorem HelpSng_eval_theta (t : Fv I.F p ⊗[I.F] I.E) :
    tensMap (E := I.E) (evalV I.F p) (thetaP I p t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [localTheta_tmul, tensMap_tmul_lemma_2]
    show singleV I.F p a p ⊗ₜ[I.F] b = a ⊗ₜ[I.F] b
    rw [Comp_single_same]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem HelpSng_eval_theta_ne (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) (t : Fv I.F p ⊗[I.F] I.E) :
    tensMap (E := I.E) (evalV I.F v) (thetaP I p t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [localTheta_tmul, tensMap_tmul_lemma_2]
    show singleV I.F p a v ⊗ₜ[I.F] b = 0
    rw [Comp_single_ne I p v hv, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem HelpSng_eval_e : tensMap (E := I.E) (evalV I.F p) (eP I p) = 1 := by
  show tensMap (E := I.E) (evalV I.F p) (chi I p ⊗ₜ[I.F] (1 : I.E)) = 1
  rw [tensMap_tmul_lemma_2]
  show singleV I.F p 1 p ⊗ₜ[I.F] (1 : I.E) = 1
  rw [Comp_single_same, Algebra.TensorProduct.one_def]

theorem HelpSng_eval_e_ne (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) :
    tensMap (E := I.E) (evalV I.F v) (eP I p) = 0 := by
  show tensMap (E := I.E) (evalV I.F v) (chi I p ⊗ₜ[I.F] (1 : I.E)) = 0
  rw [tensMap_tmul_lemma_2]
  show singleV I.F p 1 v ⊗ₜ[I.F] (1 : I.E) = 0
  rw [Comp_single_ne I p v hv, TensorProduct.zero_tmul]

theorem HelpSng_e_theta (t : Fv I.F p ⊗[I.F] I.E) : eP I p * thetaP I p t = thetaP I p t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero]
  | tmul a b =>
    rw [localTheta_tmul]
    show (chi I p ⊗ₜ[I.F] (1 : I.E)) * (sL I p a ⊗ₜ[I.F] b) = sL I p a ⊗ₜ[I.F] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, show chi I p = sL I p 1 from rfl,
      ← HelpSng_sL_mul, one_mul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem idempotent_complement_mul (t : Fv I.F p ⊗[I.F] I.E) : (1 - eP I p) * thetaP I p t = 0 := by
  rw [sub_mul, one_mul, HelpSng_e_theta, sub_self]

theorem HelpSng_e_idem : eP I p * eP I p = eP I p := by
  have h := HelpSng_e_theta I p 1
  rwa [HelpSng_theta_one] at h

theorem idempotent_complement_idem : (1 - eP I p) * (1 - eP I p) = 1 - eP I p := by
  rw [sub_mul, one_mul, mul_sub, mul_one, HelpSng_e_idem, sub_self, sub_zero]

private theorem sigR_tmul_lemma_3 {R : Type} [CommRing R] [Algebra I.F R] (a : R) (b : I.E) :
    sigR R I.cm.sig (a ⊗ₜ[I.F] b) = a ⊗ₜ[I.F] I.cm.sig b := rfl

theorem HelpSng_sig_e : sigR (Af I.F) I.cm.sig (eP I p) = eP I p := by
  show sigR (Af I.F) I.cm.sig (chi I p ⊗ₜ[I.F] (1 : I.E)) = chi I p ⊗ₜ[I.F] (1 : I.E)
  rw [sigR_tmul_lemma_3, map_one]

theorem HelpSng_sig_theta (t : Fv I.F p ⊗[I.F] I.E) :
    sigR (Af I.F) I.cm.sig (thetaP I p t) = thetaP I p (sigR (Fv I.F p) I.cm.sig t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [localTheta_tmul, sigR_tmul_lemma_3, sigR_tmul_lemma_3, localTheta_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

def mixM {m o : Type} (A : Matrix m o (Af I.F ⊗[I.F] I.E)) (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) :
    Matrix m o (Af I.F ⊗[I.F] I.E) :=
  (1 - eP I p) • A + K.map (thetaP I p)

theorem HelpSng_mix_mul {m o q : Type} [Fintype o] (A : Matrix m o (Af I.F ⊗[I.F] I.E))
    (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) (B : Matrix o q (Af I.F ⊗[I.F] I.E))
    (L : Matrix o q (Fv I.F p ⊗[I.F] I.E)) :
    mixM I p A K * mixM I p B L = mixM I p (A * B) (K * L) := by
  ext i j
  simp only [mixM, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    map_sum, Finset.mul_sum, HelpSng_theta_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  linear_combination (A i k * B k j) * idempotent_complement_idem I p + A i k * idempotent_complement_mul I p (L k j) +
    B k j * idempotent_complement_mul I p (K i k)

theorem HelpSng_mix_one {m : Type} [DecidableEq m] :
    mixM I p (1 : Matrix m m (Af I.F ⊗[I.F] I.E)) (1 : Matrix m m (Fv I.F p ⊗[I.F] I.E)) = 1 := by
  ext i j
  simp only [mixM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs
  · rw [HelpSng_theta_one]; ring
  · rw [map_zero]; ring

theorem HelpSng_JR_split :
    mixM I p (JR (Af I.F) I.J) (JR (Fv I.F p) I.J) = JR (Af I.F) I.J := by
  ext i j
  show (1 - eP I p) * inclR (Af I.F) (I.J i j) + thetaP I p (inclR (Fv I.F p) (I.J i j)) =
    inclR (Af I.F) (I.J i j)
  rw [HelpSng_theta_inclR]
  ring

theorem HelpSng_cT_mix {m o : Type} (A : Matrix m o (Af I.F ⊗[I.F] I.E))
    (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) :
    Formalism.UG.cT (sigR (Af I.F) I.cm.sig) (mixM I p A K) =
      mixM I p (Formalism.UG.cT (sigR (Af I.F) I.cm.sig) A) (Formalism.UG.cT (sigR (Fv I.F p) I.cm.sig) K) := by
  ext i j
  show sigR (Af I.F) I.cm.sig (mixM I p A K j i) = mixM I p (Formalism.UG.cT (sigR (Af I.F) I.cm.sig) A)
    (Formalism.UG.cT (sigR (Fv I.F p) I.cm.sig) K) i j
  simp only [mixM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, HelpSng_sig_e, HelpSng_sig_theta]
  rfl

theorem HelpSng_cT_one :
    Formalism.UG.cT (sigR (Af I.F) I.cm.sig) (1 : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) = 1 := by
  show ((1 : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (sigR (Af I.F) I.cm.sig))ᵀ = 1
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

def sngGL (k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E) where
  val := mixM I p 1 (k : Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))
  inv := mixM I p 1 ((k⁻¹ : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _)
  val_inv := by rw [HelpSng_mix_mul, Matrix.one_mul, Units.mul_inv, HelpSng_mix_one]
  inv_val := by rw [HelpSng_mix_mul, Matrix.one_mul, Units.inv_mul, HelpSng_mix_one]

theorem HelpSng_unitary (k : HA (Fv I.F p) I.cm.sig I.J) :
    sngGL I p (HA.mat (Fv I.F p) I.cm.sig I.J k) ∈ HR (Af I.F) I.cm.sig I.J := by
  have hK : Formalism.UG.cT (sigR (Fv I.F p) I.cm.sig)
      ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) * JR (Fv I.F p) I.J *
      ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) = JR (Fv I.F p) I.J := k.2
  show Formalism.UG.cT (sigR (Af I.F) I.cm.sig) (mixM I p 1 _) * JR (Af I.F) I.J * mixM I p 1 _ = JR (Af I.F) I.J
  conv_lhs => rw [← HelpSng_JR_split I p]
  rw [HelpSng_cT_mix, HelpSng_mix_mul, HelpSng_mix_mul, hK, HelpSng_cT_one, Matrix.one_mul,
    Matrix.mul_one, HelpSng_JR_split]

def sngHA (k : HA (Fv I.F p) I.cm.sig I.J) : HA (Af I.F) I.cm.sig I.J :=
  ⟨sngGL I p (HA.mat (Fv I.F p) I.cm.sig I.J k), HelpSng_unitary I p k⟩

theorem HelpSng_piV_same (k : HA (Fv I.F p) I.cm.sig I.J) : piV I p (sngHA I p k) = k := by
  apply Subtype.ext
  apply Units.ext
  show (mixM I p 1 ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))).map (tensMap (E := I.E) (evalV I.F p)) =
    ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))
  ext i j
  simp only [Matrix.map_apply, mixM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, HelpSng_eval_e, HelpSng_eval_theta, sub_self, zero_mul, zero_add]

theorem HelpSng_piV_ne (k : HA (Fv I.F p) I.cm.sig I.J) (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) :
    piV I v (sngHA I p k) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (mixM I p 1 ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))).map (tensMap (E := I.E) (evalV I.F v)) = 1
  ext i j
  simp only [Matrix.map_apply, mixM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, HelpSng_eval_e_ne I p v hv, HelpSng_eval_theta_ne I p v hv, sub_zero, one_mul,
    add_zero]
  rcases eq_or_ne i j with h | h <;> simp [Matrix.one_apply, h]

theorem HelpSng_mem_Kf (k : HA (Fv I.F p) I.cm.sig I.J)
    (hk : k ∈ Kv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) p) :
    sngHA I p k ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) := by
  refine Subgroup.mem_iInf.mpr (fun v => ?_)
  show HA.mat (Fv I.F v) I.cm.sig I.J (piV I v (sngHA I p k)) ∈ Kloc v (I.L : Set (Fin I.n → I.E))
  by_cases hv : v = p
  · subst hv
    rw [HelpSng_piV_same]
    exact hk
  · rw [HelpSng_piV_ne I p k v hv]
    exact Subgroup.one_mem _

theorem single_component_surjective : SngSurj := by
  intro I p k hk
  exact ⟨sngHA I p k, HelpSng_mem_Kf I p k hk, HelpSng_piV_same I p k, fun v hv => HelpSng_piV_ne I p k v hv⟩

end PI.MassDataKppVolLemmas
