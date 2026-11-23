import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop.LComm
variable {D : D7}
end GlobalTheory.MiTop.LComm
end
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.linkComm_of_laws_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f k _ _ _ _ ι o ε S₀ hU hc ht hnd _ hinj hne h0 hsur n h
  have hall : ∀ η : ι → 𝓀[k]ˣ, ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧
      ∀ φ y, (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u (S φ)).1 y =
        o.S (fun _ => η) 0 ((chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) := by
    intro η
    obtain ⟨α⟩ := hne W.P.A3.A.μ0
    have hR := (ht W.P.A3.A.μ0).2.2.2.2
    refine GlobalTheory.T.levelPrime_operators_stepZero_scale_norms D u (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ hc.inf hU (hc.x 0 (Nat.zero_le _)).cpt k ι o.p o.I o.q o.χ o.hχ (o.β 0) (o.Q 0)
      hnd hinj (fun φ y i => ?_) η (fun φ => ?_)
    · have := (hR.ram 0 (Nat.zero_le _) _ (h0 _ φ).1 α y).2 i
      rw [(h0 _ φ).2 α y] at this
      exact this
    · obtain ⟨h1, h2⟩ := hR.S₀ η _ (h0 _ φ).1
      obtain ⟨φ', e⟩ := hsur _ _ h1
      refine ⟨φ', fun y => ?_⟩
      have := h2 α y
      rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
      exact this
  choose S r hr hS hrd using hall
  have hS0 : ∀ t η φ, S₀ t η (_root_.GlobalTheory.MiTop.col0_alt f t φ) = _root_.GlobalTheory.MiTop.col0_alt f t (S η φ) := by
    intro t η φ
    obtain ⟨α⟩ := hne t
    obtain ⟨h1, h2⟩ := (ht t).2.2.2.2.S₀ η _ (h0 t φ).1
    obtain ⟨φ', e⟩ := hsur _ _ h1
    rw [e]
    congr 1
    apply (D.eMu u).injective
    apply Subtype.ext
    refine LComm.chart0_inj (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ _ _ (fun y => ?_)
    have := h2 α y
    rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
    rw [this, hrd]
  obtain ⟨A, a, ha, hA, hA'⟩ := LComm.iter_equiv S r hr hS ε n
  refine ⟨A, a, o.cS n, ha, hA, ?_, fun t φ F => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ ?_
    refine Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne'
    exact Nat.cast_pos.2 Nat.card_pos
  · obtain ⟨t1, t2, t3, t4, t5⟩ := ht t
    rw [GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero D f.c k ι o (f.t t) ε (S₀ t) t1 t2 t3 t4 t5 n h _ (h0 t φ).1 F,
      LComm.iterS_comm (fun η φ => S η φ) (S₀ t) (_root_.GlobalTheory.MiTop.col0_alt f t) (hS0 t) ε n φ, hA']
end
