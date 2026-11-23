import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

open Classical in

theorem avg_level (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (G : Type) [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (f : V) (h : P) :
    r h ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) =
      ((ψ h : Kˣ) : K) • ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) := by
  have key : ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r h (r p f) = ((ψ h : Kˣ) : K) • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun p => ?_
    simp only [Equiv.coe_mulLeft, smul_smul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    rw [_root_.mul_inv_rev, map_mul, map_inv, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  rw [map_smul, map_sum, smul_comm]
  simp only [map_smul]
  rw [key]

set_option maxHeartbeats 1000000 in

theorem jR_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (f : A.fam.amb.FR t), (∀ h : (F.lvl b).P, (A.fam.R t).r h f = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) → ∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), R.B.jR t f (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • R.B.jR t f h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t f hf q hq h
  have e : (R.B.R t).pres.extL (A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f) =
      Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q ((R.B.R t).pres.extL f) :=
    (R.B.R t).act_tie.act_eq ((R.B.R t).act_tie.red q) q rfl f
  have hf' : A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f = (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f := hf ⟨_, hq⟩
  have e3 := congrArg (R.B.R t).pres.extL hf'
  have e4 : (R.B.R t).pres.extL ((((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f) =
      D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • (R.B.R t).pres.extL f :=
    map_smulₛₗ (R.B.R t).pres.extL _ f
  have e5 := congrFun ((e4.symm.trans e3.symm).trans e) h
  simp only [Bridge.g0Act, Pi.smul_apply] at e5
  have e7 := congrArg (fun w => (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂˣ) : ℂ) • w) e5
  simp only [smul_smul, Units.mul_inv, one_smul] at e7
  exact e7.symm

end GlobalTheory.TopSpan
