import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AnnNbhdCpt

variable {D : D7}

theorem pairA_add_one : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_add, map_one, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, zero_add])
    (by rw [map_add, map_one, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, add_zero])

theorem pairA_mul_pairA : pairA D.host.F 1 0 * pairA D.host.F 0 1 = 0 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, mul_zero])
    (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, zero_mul])

theorem smul_fin_add (z : AE D) : pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z = z := by
  rw [← add_smul, pairA_add_one, one_smul]

theorem smul_fin_of_inf (z : AE D) (h : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h' := (GlobalTheory.AdelicCoord.infPart_eq_zero_iff D z).1 h
  have := smul_fin_add z
  rwa [h', add_zero] at this

theorem infPart_smul_fin (z : AE D) : infPart D (pairA D.host.F 0 1 • z) = 0 := by
  rw [GlobalTheory.AdelicCoord.infPart_eq_zero_iff, smul_smul, pairA_mul_pairA, zero_smul]

theorem mem_idAt_true (z : AE D) : z ∈ idAt D (fun _ => True) ↔ infPart D z = 0 := by
  unfold idAt
  rw [Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w => absurd trivial w.2⟩⟩

theorem mxAt_true_iff {m n : ℕ} (x : Mx D m n) : MxAt (fun _ => True) x ↔ pairA D.host.F 1 0 • x = 0 := by
  unfold MxAt
  rw [← Matrix.ext_iff]
  simp only [Matrix.smul_apply, Matrix.zero_apply, mem_idAt_true, GlobalTheory.AdelicCoord.infPart_eq_zero_iff]

theorem continuous_smul_mx {m n : ℕ} (c : AF D.host.F) : Continuous fun x : Mx D m n => c • x := by
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun x : Mx D m n => c • x i j
  simp only [Algebra.smul_def]
  exact continuous_const.mul (continuous_id.matrix_elem i j)

def annSet (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO S T u u') = 1}

set_option maxHeartbeats 1000000 in

theorem isCompact_annSet (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Γ : AddSubgroup (WO S T)) (U : Set (WO S T)) (hU : IsOpen U) (h0 : (0 : WO S T) ∈ U)
    (hUΓ : ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ Γ) : IsCompact (annSet ψ Γ) := by
  obtain ⟨h1, h2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  let e : AF D.host.F := pairA D.host.F 0 1
  let V : AddSubgroup (WO S T) :=
    { carrier := {u | e • u ∈ Γ}
      add_mem' := fun {a b} ha hb => by show e • (a + b) ∈ Γ; rw [smul_add]; exact add_mem ha hb
      zero_mem' := by show e • (0 : WO S T) ∈ Γ; rw [smul_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by show e • (-a) ∈ Γ; rw [smul_neg]; exact neg_mem ha }
  have hfinE : ∀ u : WO S T, MxAt (fun _ => True) (e • u) := fun u i j => by
    rw [mem_idAt_true, Matrix.smul_apply]; exact infPart_smul_fin _
  have hVo : IsOpen (V : Set (WO S T)) := by
    refine AddSubgroup.isOpen_of_mem_nhds V (g := 0) ?_
    refine Filter.mem_of_superset (((continuous_smul_mx e).isOpen_preimage U hU).mem_nhds (by
      show e • (0 : WO S T) ∈ U; rw [smul_zero]; exact h0)) fun u hu => hUΓ _ hu (hfinE u)
  obtain ⟨Q, hQc, hQ⟩ := GlobalTheory.AnnihMat.annihilator_inBox_full D ψ hψ S T V hVo
  have hfix : ∀ u : WO S T, MxAt (fun _ => True) u → e • u = u := fun u hu => by
    ext i j
    rw [Matrix.smul_apply]
    exact smul_fin_of_inf _ ((mem_idAt_true _).1 (hu i j))
  have hsub : annSet ψ Γ ⊆ (fun x : WO S T => e • x) '' Q := by
    rintro u' ⟨hfin, hann⟩
    obtain ⟨k, hk, hk0⟩ := hQ u' fun u hu hu0 => by
      have hu1 : MxAt (fun _ => True) u := fun i j => by
        rw [mem_idAt_true]; exact congrFun (congrFun hu0 i) j
      have : u ∈ Γ := by
        have h := hu
        change e • u ∈ Γ at h
        rwa [hfix u hu1] at h
      exact (psi_symplO_swap ψ _ _).2 (hann u this)
    refine ⟨k, hk, ?_⟩
    have hd : e • (u' - k) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      exact (GlobalTheory.AdelicCoord.finPart_eq_zero_iff D _).1 (congrFun (congrFun hk0 i) j)
    rw [smul_sub, sub_eq_zero] at hd
    show e • k = u'
    rw [← hd, hfix u' hfin]
  have hcl : IsClosed (annSet ψ Γ) := by
    have e1 : annSet ψ Γ = {x : WO S T | pairA D.host.F 1 0 • x = 0} ∩
        ⋂ u ∈ Γ, {x : WO S T | ψ (symplO S T u x) = 1} := by
      ext x
      simp only [annSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mxAt_true_iff]
    rw [e1]
    refine IsClosed.inter (isClosed_eq (continuous_smul_mx _) continuous_const)
      (isClosed_biInter fun u _ => isClosed_eq ?_ continuous_const)
    exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const continuous_id)
  exact (hQc.image (continuous_smul_mx e)).of_isClosed_subset hcl hsub

end GlobalTheory.AnnNbhdCpt

end
