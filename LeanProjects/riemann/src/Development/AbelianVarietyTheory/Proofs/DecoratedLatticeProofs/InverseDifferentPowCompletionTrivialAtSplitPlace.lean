import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.DiUnit

variable {D : D7}

theorem eq_one_iff {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} : idV 𝔞 v = idV 1 v ↔
    ∀ s, s ∈ idV 𝔞 v ↔ incA D (1 : D.host.E)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  simp only [inv_one, map_one, one_mul]
  constructor
  · intro h s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => ⟨h, h.1⟩, fun h => h.1⟩
  · intro h
    ext s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem mul_eq_one {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (h1 : idV 𝔞 v = idV 1 v) (h2 : idV 𝔟 v = idV 1 v) :
    idV (𝔞 * 𝔟) v = idV 1 v := by
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔟 1 1 one_ne_zero one_ne_zero (eq_one_iff.1 h1) (eq_one_iff.1 h2)
  rw [mul_one] at this
  exact eq_one_iff.2 this

theorem pow_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) (n : ℕ) : idV (𝔞 ^ n) v = idV 1 v := by
  induction n with
  | zero => rw [pow_zero]
  | succ n ih => rw [pow_succ]; exact mul_eq_one ih h

theorem inv_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) : idV 𝔞⁻¹ v = idV 1 v := by
  have h0 : 𝔞 ≠ 0 := fun e =>
    GlobalTheory.SeeSaw.LiftModel.idV_ne_bot (one_ne_zero (α := FI D)) v (by rw [← h, e, GlobalTheory.SeeSaw.idV_zero])
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h0)
  have h1 := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ 1 y one_ne_zero hy0 (eq_one_iff.1 h) hy
  rw [mul_inv_cancel₀ h0, one_mul] at h1
  ext s
  rw [hy, ← h1]

theorem AAbar_eq_one {v : GlobalTheory.FinPl.Pl D} (hA : idV D.host.AA v = idV 1 v) : idV D.host.AAbar v = idV 1 v := by
  ext s
  have h1 := GlobalTheory.SeeSaw.idV_cA_iff D v D.host.AA (cA D s)
  rw [GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.conjFI_AA] at h1
  have h2 := GlobalTheory.SeeSaw.idV_cA_iff D v 1 s
  rw [map_one] at h2
  rw [← h1, hA, h2]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace (p : SplitPt D k) (hp : p.UnitAA) :
    idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v = idV 1 p.v := by
  have hx : D.host.xi0 ≠ 0 := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  ext s
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  constructor
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
      have e : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (r • D.host.xi0) : AE D) =
          incA D D.host.xi0 * (pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E r) := by
        rw [GlobalTheory.IdVGen.incA_mul_tmul, Algebra.smul_def, mul_comm (algebraMap (𝓞 D.host.E) D.host.E r)]
      rw [e]
      exact (hp.1 _ (GlobalTheory.IdVGen.gen_mem_intAt hα hαv r)).1
    | zero => exact GlobalTheory.IdVGen.intAt_zero' _
    | add a b _ _ ha hb => exact GlobalTheory.IdVGen.intAt_add' ha hb
    | neg a _ ha => exact GlobalTheory.IdVGen.intAt_neg' ha
  · intro hs
    have h3 := (GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 (hp.1 s hs).2
    have key : ∀ y ∈ idV (1 : FI D) p.v,
        incA D D.host.xi0 * y ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
        rw [GlobalTheory.IdVGen.incA_mul_tmul]
        refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
        exact (FractionalIdeal.mem_spanSingleton _).2 ⟨o, by rw [Algebra.smul_def]; exact mul_comm _ _⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at this

theorem AA_eq_one (p : SplitPt D k) (hp : p.UnitAA) : idV D.host.AA p.v = idV 1 p.v := by
  let L : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1
  let ζ : Fin L.rank → D.host.E := fun _ => 1
  have hζ : ζ ≠ 0 := fun e => one_ne_zero (congrFun e (0 : Fin 1))
  have e : GlobalTheory.FinPl.latA L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 1) (· = p.v) =
      latV L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ D.host.AA) (· = p.v) := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    congr 1
    ext y
    constructor
    · rintro ⟨α, h1, h2, a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, 1, rfl, _, ⟨a * c, ?_, rfl⟩, ?_⟩
      · have := FractionalIdeal.mul_mem_mul (S := nonZeroDivisors (𝓞 D.host.E)) (I := D.host.AA) (J := 1) ha hc
        rwa [mul_one] at this
      · funext i; simp [mul_assoc]
    · rintro ⟨α, h1, h2, _, rfl, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, c, hc, _, ⟨1, FractionalIdeal.one_mem_one _, rfl⟩, ?_⟩
      funext i; simp
  have key : ∀ s ∈ idAt D (· = p.v), s ∈ idV D.host.AA p.v ↔ s ∈ idV 1 p.v := fun s hs => by
    rw [← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ D.host.AA p.v s hs,
      ← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ 1 p.v s hs, ← e, hp.2]
  ext s
  exact ⟨fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).1 h,
    fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).2 h⟩

end GlobalTheory.Core.Mi.LatMatch.DiUnit

open GlobalTheory.Core.Mi.LatMatch.DiUnit in

theorem GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  intro D k _ _ _ _ p hp n a
  have hd : idV (dI D) p.v = idV 1 p.v := by
    have hA := AA_eq_one p hp
    unfold GlobalTheory.SeeSaw.dI
    exact mul_eq_one (mul_eq_one (fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace p hp) hA) (AAbar_eq_one hA)
  have h1 := pow_eq_one hd n
  have h2 := inv_eq_one h1
  exact ⟨by rw [h1, GlobalTheory.SeeSaw.idV_one_eq_intAt], by rw [h2, GlobalTheory.SeeSaw.idV_one_eq_intAt]⟩

end
