import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

abbrev Ev (D : D7) (v : Pl D) : Type := Fv D.host.F v ⊗[D.host.F] D.host.E

def cf (v : Pl D) : AfE D →ₐ[D.host.F] Ev D v :=
  Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)

theorem cf_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) : cf v (a ⊗ₜ[D.host.F] x) = evalV D.host.F v a ⊗ₜ[D.host.F] x :=
  rfl

theorem cv_eq (v : Pl D) (x : AE D) : cv D v x = cf v (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | tmul a y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, map_add, hx, hy]

theorem cf_mem_of_mem {z : AfE D} (hz : z ∈ intAE D) (v : Pl D) : cf v z ∈ intLoc D.host.F D.host.E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [cf_tmul]
    exact tmul_mem_intLoc (ha v) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def pr (φ : D.host.E →ₗ[D.host.F] D.host.F) : AfE D →ₗ[D.host.F] Af D.host.F :=
  (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ φ.lTensor (Af D.host.F)

theorem pr_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (a : Af D.host.F) (x : D.host.E) :
    pr φ (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [pr, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

def aux₃ (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) : Ev D v →ₗ[D.host.F] Fv D.host.F v :=
  (TensorProduct.rid D.host.F (Fv D.host.F v)).toLinearMap ∘ₗ φ.lTensor (Fv D.host.F v)

theorem trace_projection_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (a : Fv D.host.F v) (x : D.host.E) :
    aux₃ φ v (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [aux₃, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

theorem evalV_pr (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (y : AfE D) :
    evalV D.host.F v (pr φ y) = aux₃ φ v (cf v y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, map_zero, map_zero, LinearMap.map_zero]
  | tmul a x => rw [pr_tmul, cf_tmul, trace_projection_tmul, AlgHom.map_smul_of_tower]
  | add y y' hy hy' => rw [LinearMap.map_add, map_add, map_add, LinearMap.map_add, hy, hy']

theorem trace_projection_mem_integers (φ : D.host.E →ₗ[D.host.F] D.host.F) (hφ : ∀ x : 𝓞 D.host.E, φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range)
    (v : Pl D) {w : Ev D v} (hw : w ∈ intLoc D.host.F D.host.E v) : aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F := by
  refine intLoc_induction (p := fun w => aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F) (fun a ha x => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hw
  · obtain ⟨r, hr⟩ := hφ x
    rw [trace_projection_tmul, ← hr, Algebra.smul_def]
    exact mul_mem (v.coe_mem_adicCompletionIntegers r) ha
  · rw [LinearMap.map_zero]; exact zero_mem _
  · rw [LinearMap.map_add]; exact add_mem hy hz
  · rw [LinearMap.map_neg]; exact neg_mem hy

theorem sum_pr {k : ℕ} (s : Fin k → 𝓞 D.host.E) (φ : Fin k → D.host.E →ₗ[D.host.F] D.host.F)
    (hsum : ∀ x, ∑ j, φ j x • (s j : D.host.E) = x) (y : AfE D) :
    ∑ j, pr (φ j) y ⊗ₜ[D.host.F] ((s j : D.host.E)) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | tmul a x =>
    simp only [pr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hsum x]
  | add y y' hy hy' => simp only [LinearMap.map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hy, hy']

theorem mem_of_cf_mem {z : AfE D} (hz : ∀ v : Pl D, cf v z ∈ intLoc D.host.F D.host.E v) : z ∈ intAE D := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := D.host.F) (E := D.host.E)
  rw [← sum_pr s φ hsum z]
  refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨pr (φ j) z, fun v => ?_, s j, rfl⟩
  rw [evalV_pr]
  exact trace_projection_mem_integers (φ j) (fun x => hφ x j) v (hz v)

theorem exists_nat_mul_mem {Q : Set (AfE D)} (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ Q, (N : AfE D) * q ∈ intAE D := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun n : ℕ => {q : AfE D | ((n + 1 : ℕ) : AfE D) * q ∈ intAE D})
    (fun n => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_const.mul continuous_id))
    (fun q _ => by
      obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE q
      exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun _ _ => Nat.succ_pos _, fun q hq => ?_⟩
  obtain ⟨n, hn, hq'⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [← Finset.mul_prod_erase t _ hn, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : AfE D), mul_assoc]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE _) hq'

def U (S : Finset (Pl D)) (ef : AfE D) (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (AfE D)) where
  carrier := {w | (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D}
  add_mem' := fun {a b} ha hb => ⟨fun v hv i j => by
      rw [Matrix.add_apply, map_add]; exact add_mem (ha.1 v hv i j) (hb.1 v hv i j),
    fun i j => by rw [Matrix.add_apply, mul_add, mul_add]; exact add_mem (ha.2 i j) (hb.2 i j)⟩
  zero_mem' := ⟨fun v _ i j => by rw [Matrix.zero_apply, map_zero]; exact zero_mem _,
    fun i j => by rw [Matrix.zero_apply, mul_zero, mul_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun v hv i j => by rw [Matrix.neg_apply, map_neg]; exact neg_mem (ha.1 v hv i j),
    fun i j => by rw [Matrix.neg_apply, mul_neg, mul_neg]; exact neg_mem (ha.2 i j)⟩

theorem mem_U {S : Finset (Pl D)} {ef : AfE D} {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)} :
    w ∈ U S ef N m n ↔ (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D := Iff.rfl

open Classical in

theorem mem_U_iff {S : Finset (Pl D)} {ef : AfE D} (hef : ef * ef = ef)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)}
    (hw : ∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) :
    w ∈ U S ef N m n ↔ (Matrix.of fun i j => ef * w i j) ∈ U S ef N m n := by
  have h2 : ∀ i j, (N : AfE D) * (ef * (Matrix.of fun i j => ef * w i j) i j) = (N : AfE D) * (ef * w i j) :=
    fun i j => by rw [Matrix.of_apply, ← mul_assoc ef ef, hef]
  rw [mem_U, mem_U]
  simp only [h2]
  refine ⟨fun h => ⟨fun v hv i j => ?_, h.2⟩, fun h => ⟨hw, h.2⟩⟩
  rw [Matrix.of_apply, map_mul, hS v, if_neg hv, zero_mul]
  exact zero_mem _

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
