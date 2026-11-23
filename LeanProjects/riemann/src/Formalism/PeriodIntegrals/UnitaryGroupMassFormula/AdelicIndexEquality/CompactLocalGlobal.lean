import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem matV_coe (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ((matV I v g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I v).toRingHom := rfl

private theorem eq_of_forall_evalV_eq {F : Type} [Field F] [NumberField F] (a b : Af F)
    (h : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b) : a = b :=
  Subtype.ext (funext fun v => h v)

private theorem tensorBasis_repr_psiV_eq_evalV_repr_comm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : I.E ⊗[I.F] Af I.F) (i : Module.Free.ChooseBasisIndex I.F I.E) :
    (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Free.chooseBasis I.F I.E)).repr
        (PI.FinKW.psiV I v z) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        ((Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr
          (Algebra.TensorProduct.comm I.F I.E (Af I.F) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [PI.FinKW.psiV, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem mat_ext_of_psiV (I : AutInst) (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (h : ∀ v, M.map (PI.FinKW.psiV I v).toRingHom = N.map (PI.FinKW.psiV I v).toRingHom) :
    M = N := by
  ext i j
  have hij : ∀ v, PI.FinKW.psiV I v (M i j) = PI.FinKW.psiV I v (N i j) := fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa [Matrix.map_apply] using this
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  apply (Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr.injective
  refine Finsupp.ext fun k => ?_
  apply eq_of_forall_evalV_eq
  intro v
  rw [← tensorBasis_repr_psiV_eq_evalV_repr_comm, ← tensorBasis_repr_psiV_eq_evalV_repr_comm, hij v]

theorem matrix_v_injective : MatVInj := by
  unfold MatVInj
  intro I y z h
  apply Subtype.ext
  apply Units.ext
  apply mat_ext_of_psiV I
  intro v
  have := congrArg Units.val (h v)
  simpa only [matV_coe] using this

theorem psiV_sigR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) z) = sigV I v (PI.FinKW.psiV I v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigV]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I v e := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclV]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) {m p : Type} (M : Matrix m p A) :
    (Formalism.UG.cT σ M).map f = Formalism.UG.cT τ (M.map f) := by
  ext i j
  simp [Formalism.UG.cT, hf]

theorem mapJ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I v).toRingHom =
      I.J.map (inclV I v) := by
  ext i j
  simp only [Matrix.map_apply]
  exact psiV_inclE I v _

theorem map_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul,
    map_cT (PI.FinKW.psiV I v).toRingHom (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigV I v)
      (fun a => psiV_sigR I v a), mapJ]

theorem mem_Uv_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    g ∈ Uv I v ↔ Formalism.UG.cT (sigV I v) g.val * I.J.map (inclV I v) * g.val = I.J.map (inclV I v) := Iff.rfl

theorem mem_Gf_iff (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) ↔
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) g.val * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        g.val = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := Iff.rfl

theorem matrix_v_unitary : MatVU := by
  unfold MatVU
  intro I v y
  rw [mem_Uv_iff, matV_coe]
  have hy := (mem_Gf_iff I y).1 y.2
  rw [← map_unitary, hy]
  exact mapJ I v

theorem vecV_mulVec' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ x) = M.map (PI.FinKW.psiV I v).toRingHom *ᵥ PI.FinKW.vecV I v x := by
  funext i
  simp [PI.FinKW.vecV, Matrix.mulVec, dotProduct, map_sum]

theorem stab_iff_loc (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.stabGL I.Lf ↔ ∀ v, matV I v g ∈ Kv I v := by
  have hL : ∀ x, x ∈ I.Lf ↔
      ∀ v, PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨PI.FinKW.LocTo.mem_local_lattice_iff I x, PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := PI.FinKW.local_vector_lift I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : (g : Matrix _ _ _) *ᵥ x ∈ I.Lf ↔
        ((matV I v g : GL (Fin I.n) _) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL, matV_coe]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec', hxv] at this
      · intro H w
        rw [vecV_mulVec']
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    show x ∈ I.Lf ↔ (g : Matrix _ _ _) *ᵥ x ∈ I.Lf
    rw [hL x, hL ((g : Matrix _ _ _) *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec', ← matV_coe]
    exact hK v (PI.FinKW.vecV I v x)

theorem compact_local_global : KLocGlob := by
  unfold KLocGlob
  intro I y
  rw [PI.AdIndexEq.Ksub, Subgroup.mem_comap]
  exact stab_iff_loc I _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
