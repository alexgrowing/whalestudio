import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocBEOfNatCast

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst)

theorem Comp_mul_apply (a b : Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) : (a * b) v = a v * b v := rfl
theorem Comp_add_apply (a b : Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) : (a + b) v = a v + b v := rfl
theorem Comp_sub_apply (a b : Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) : (a - b) v = a v - b v := rfl
theorem Comp_one_apply (v : HeightOneSpectrum (𝓞 I.F)) : (1 : Af I.F) v = 1 := rfl
theorem Comp_zero_apply (v : HeightOneSpectrum (𝓞 I.F)) : (0 : Af I.F) v = 0 := rfl
theorem Comp_evalV (v : HeightOneSpectrum (𝓞 I.F)) (a : Af I.F) : evalV I.F v a = a v := rfl

theorem Comp_single_same (p : HeightOneSpectrum (𝓞 I.F)) (y : Fv I.F p) : singleV I.F p y p = y := by
  classical
  exact Pi.single_eq_same (M := fun w => Fv I.F w) p y

theorem Comp_single_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) (y : Fv I.F p) :
    singleV I.F p y v = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w => Fv I.F w) h y

def chi (p : HeightOneSpectrum (𝓞 I.F)) : Af I.F := singleV I.F p 1

theorem Comp_chi_same (p : HeightOneSpectrum (𝓞 I.F)) : chi I p p = 1 := Comp_single_same I p 1

theorem Comp_chi_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) : chi I p v = 0 :=
  Comp_single_ne I p v h 1

theorem Comp_chi_idem (p : HeightOneSpectrum (𝓞 I.F)) : chi I p * chi I p = chi I p := by
  apply FiniteAdeleRing.ext
  intro v
  rw [Comp_mul_apply]
  by_cases h : v = p
  · subst h; rw [Comp_chi_same]; simp
  · rw [Comp_chi_ne I p v h]; simp

theorem Comp_chi_orth (p q : HeightOneSpectrum (𝓞 I.F)) (hpq : p ≠ q) : chi I p * chi I q = 0 := by
  apply FiniteAdeleRing.ext
  intro v
  rw [Comp_mul_apply, Comp_zero_apply]
  by_cases h : v = p
  · subst h; rw [Comp_chi_ne I q v hpq]; simp
  · rw [Comp_chi_ne I p v h]; simp

theorem Comp_chi_int (p : HeightOneSpectrum (𝓞 I.F)) : chi I p ∈ Formalism.UG.intAd I.F := by
  intro v
  by_cases h : v = p
  · subst h; show chi I v v ∈ _; rw [Comp_chi_same]; exact one_mem _
  · show chi I p v ∈ _; rw [Comp_chi_ne I p v h]; exact zero_mem _

abbrev piV (v : HeightOneSpectrum (𝓞 I.F)) : HA (Af I.F) I.cm.sig I.J →* HA (Fv I.F v) I.cm.sig I.J :=
  haMap I.cm.sig I.J (evalV I.F v)

theorem Comp_piV_mat (v : HeightOneSpectrum (𝓞 I.F)) (h : HA (Af I.F) I.cm.sig I.J) :
    ((HA.mat (Fv I.F v) I.cm.sig I.J (piV I v h) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) =
    ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (tensMap (E := I.E) (evalV I.F v)) := rfl

variable (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I)

theorem Comp_tf_locG (a : Af I.F) (ha : a * a = a) (z : I.Gf) :
    ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb (locG I a z)) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
    locM (a ⊗ₜ[I.F] (1 : I.E)) ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb z) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) := by
  rw [Bridge_mat, Bridge_mat, LocB_fmat I a ha]
  have := Loc_locM_map ((swapE I : I.E ⊗[I.F] Af I.F ≃ₐ[I.F] Af I.F ⊗[I.F] I.E) :
    I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E) (eOf I a) (I.fmat z)
  convert this using 2 <;> rfl

def sL (p : HeightOneSpectrum (𝓞 I.F)) : Fv I.F p →ₗ[I.F] Af I.F where
  toFun := singleV I.F p
  map_add' x y := by
    apply FiniteAdeleRing.ext; intro v
    rw [Comp_add_apply]
    by_cases h : v = p
    · subst h; simp only [Comp_single_same]
    · simp only [Comp_single_ne I p v h, add_zero]
  map_smul' c y := by
    apply FiniteAdeleRing.ext; intro v
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, Comp_mul_apply,
      FiniteAdeleRing.algebraMap_apply]
    by_cases h : v = p
    · subst h; simp only [Comp_single_same]; rfl
    · simp only [Comp_single_ne I p v h, mul_zero]

def thetaP (p : HeightOneSpectrum (𝓞 I.F)) : Fv I.F p ⊗[I.F] I.E →ₗ[I.F] Af I.F ⊗[I.F] I.E :=
  TensorProduct.map (sL I p) LinearMap.id

theorem Comp_chi_mul (p : HeightOneSpectrum (𝓞 I.F)) (t : Af I.F ⊗[I.F] I.E) :
    (chi I p ⊗ₜ[I.F] (1 : I.E)) * t = thetaP I p (tensMap (E := I.E) (evalV I.F p) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    show _ = thetaP I p ((Algebra.TensorProduct.map (evalV I.F p) (AlgHom.id I.F I.E)) (a ⊗ₜ x))
    rw [Algebra.TensorProduct.map_tmul, thetaP, TensorProduct.map_tmul]
    congr 1
    apply FiniteAdeleRing.ext; intro v
    rw [Comp_mul_apply]
    show _ = singleV I.F p (a p) v
    by_cases h : v = p
    · subst h; rw [Comp_chi_same, Comp_single_same, one_mul]
    · rw [Comp_chi_ne I p v h, Comp_single_ne I p v h, zero_mul]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]

theorem Comp_sep (p : HeightOneSpectrum (𝓞 I.F)) (z w : I.Gf)
    (h : piV I p (tf I hb z) = piV I p (tf I hb w)) : locG I (chi I p) z = locG I (chi I p) w := by
  apply Bridge_tf_injective I hb
  apply Bridge_HA_ext
  rw [Comp_tf_locG I hb _ (Comp_chi_idem I p), Comp_tf_locG I hb _ (Comp_chi_idem I p)]
  have hM := congrArg (fun k => ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
    Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))) h
  simp only [Comp_piV_mat] at hM
  ext i j
  have hij := congrArg (fun M => M i j) hM
  simp only [Matrix.map_apply] at hij
  simp only [locM, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_sub]
  simp only [Comp_chi_mul]
  rw [hij]

end PI.MassDataKppVolLemmas
