import Formalism.LocalToGlobal.IndefiniteReal.PHeisThP

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem repr_snd (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k = (cE F E z k).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).2
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [sndA]
    rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem repr_fst (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) k = (cE F E z k).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).1
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [fstA]
    rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem trace_tmul (e : E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange]
  rfl

end Tens

section Sympl

variable {D : D7}

theorem cA_algebraMap (c : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) c) = algebraMap (AF D.host.F) (AE D) c := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (c ⊗ₜ[D.host.F] (1 : D.host.E)) =
    c ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  rw [Algebra.smul_def, map_mul, cA_algebraMap, ← Algebra.smul_def]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) =
    (1 : AF D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hHom_add_right (V W : HSp D) (x y y' : WA V W) :
    hHom V W x (y + y') = hHom V W x y + hHom V W x y' := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hHom_smul_right (V W : HSp D) (c : AF D.host.F) (x y : WA V W) :
    hHom V W x (c • y) = c • hHom V W x y := by
  unfold hHom
  split_ifs <;> simp only [Matrix.smul_apply, mul_smul_comm, Finset.smul_sum]

theorem hHom_add_left (V W : HSp D) (x x' y : WA V W) :
    hHom V W (x + x') y = hHom V W x y + hHom V W x' y := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hHom_smul_left (V W : HSp D) (c : AF D.host.F) (x y : WA V W) :
    hHom V W (c • x) y = c • hHom V W x y := by
  unfold hHom
  split_ifs <;> simp only [Matrix.smul_apply, cA_smul, smul_mul_assoc, Finset.smul_sum]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  simp only [symplH, Formalism.L2.Theta.sympl, hHom_add_right, mul_add, map_add]

theorem symplH_smul_left (V W : HSp D) (c : AF D.host.F) (x y : WA V W) :
    symplH V W (c • x) y = c * symplH V W x y := by
  simp only [symplH, Formalism.L2.Theta.sympl, hHom_smul_right, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  simp only [symplH, Formalism.L2.Theta.sympl, hHom_add_left, mul_add, map_add]

theorem symplH_smul_right (V W : HSp D) (c : AF D.host.F) (x y : WA V W) :
    symplH V W x (c • y) = c * symplH V W x y := by
  simp only [symplH, Formalism.L2.Theta.sympl, hHom_smul_left, mul_smul_comm, map_smul, smul_eq_mul]
  ring

def symplB (V W : HSp D) : WA V W →ₗ[AF D.host.F] WA V W →ₗ[AF D.host.F] AF D.host.F :=
  LinearMap.mk₂ (AF D.host.F) (symplH V W) (symplH_add_left V W)
    (fun c x y => by rw [symplH_smul_left, smul_eq_mul]) (symplH_add_right V W)
    (fun c x y => by rw [symplH_smul_right, smul_eq_mul])

def eV (V W : HSp D) (a : Ix V W) : WA V W :=
  Matrix.single a.1 a.2.1 (incA D (Module.finBasis D.host.F D.host.E a.2.2))

theorem sum_eV (V W : HSp D) (x : WA V W) : ∑ a, Co V W x a • eV V W a = x := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, eV, Matrix.single_apply, Fintype.sum_prod_type, Co, Phi, smul_ite,
    smul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_rhs => rw [← (bA D.host.F D.host.E).sum_repr (x i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  rfl

end Sympl

end Formalism.IndefR.PHeisTh

end
