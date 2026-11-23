import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.DiffDual

variable {D : D7}

def TrInt (D : D7) (x : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (x * o) = n

theorem mem_dI_iff (x : D.host.E) : x ∈ dI D ↔ TrInt D x := by
  rw [dI, Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) _ _ _)]
  constructor
  · intro h o
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    rw [← hn]; simp
  · intro h b hb
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨n, hn⟩ := h o
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, hn]; simp

theorem TrInt.mul {x : D.host.E} (h : TrInt D x) (o : 𝓞 D.host.E) : TrInt D (x * o) := fun o' => by
  obtain ⟨n, hn⟩ := h (o * o')
  exact ⟨n, by rw [mul_assoc]; simpa using hn⟩

theorem trInt_coe (o : 𝓞 D.host.E) : TrInt D (o : D.host.E) := fun o' => by
  have hi : IsIntegral ℤ ((o : D.host.E) * o') := o.isIntegral_coe.mul o'.isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
  exact ⟨n, hn.symm⟩

theorem chi_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F}
    (hβ : β ∈ intAf D.host.F) {x : D.host.E} (hx : TrInt D x) : Conductor.chi ψ (β ⊗ₜ[D.host.F] x) = 1 := by
  rw [Conductor.chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hβ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := hx ⟨_, hi⟩
  exact ⟨n, by rw [Algebra.smul_def, mul_comm]; exact hn⟩

theorem chi_mul_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {x : D.host.E} (hx : TrInt D x)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Conductor.chi ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact chi_tmul hψ hβ (hx.mul o)
  | zero => rw [mul_zero]; exact Conductor.chi_zero ψ
  | add y y' _ _ hy hy' => rw [mul_add, Conductor.chi_add, hy, hy', one_mul]
  | neg y _ hy =>
    have := Conductor.chi_add ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * y) (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * -y)
    rwa [← mul_add, add_neg_cancel, mul_zero, Conductor.chi_zero, hy, one_mul, eq_comm] at this

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  rw [psiE, psiE, psiE, map_add, ψ.map_add_eq_mul]

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  rw [psiE, map_zero, ψ.map_zero_eq_one]

theorem psiE_neg (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) : psiE ψ (-a) = (psiE ψ a)⁻¹ := by
  rw [psiE, psiE, map_neg, ψ.map_neg_eq_inv]

theorem forward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idV (dI D) v) : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  induction hs using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
    intro o ho
    have hinf : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a * o) = 0 := by
      rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_pair, zero_mul]
    rw [Conductor.psiE_eq_chi ψ hinf, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair]
    have e : α ⊗ₜ[D.host.F] a = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * (α ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e, mul_assoc]
    exact chi_mul_int hψ ((mem_dI_iff a).1 ha) (Conductor.mul_mem_int (Conductor.tmul_mem hα 1) ho.2)
  | zero => intro o _; rw [zero_mul, psiE_zero]
  | add x y _ _ hx hy => intro o ho; rw [add_mul, psiE_add, hx o ho, hy o ho, one_mul]
  | neg x _ hx => intro o ho; rw [neg_mul, psiE_neg, hx o ho, inv_one]

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem lift_tmul (α : Af D.host.F) (x : D.host.E) : lift D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem finPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (lift D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.finPart_pair]
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

theorem infPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (lift D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.infPart_pair]
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy, add_zero]

theorem eq_lift {s : AE D} (h : infPart D s = 0) : s = lift D (finPart D s) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h, infPart_lift, sub_zero]
  · rw [RingHom.map_sub, finPart_lift, sub_self]

theorem lift_int_mem (v : Pl D) (hε : singleV D.host.F v 1 ∈ intAf D.host.F) {u : Af D.host.F ⊗[D.host.F] D.host.E}
    (hu : u ∈ intAE D) : lift D ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u) ∈ idV (dI D) v := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, o, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf hε hβ, fun w hw => ?_, (o : D.host.E),
      (mem_dI_iff _).2 (trInt_coe o), lift_tmul _ _⟩
    rw [map_mul, Conductor.ev_ne hw, zero_mul]
  | zero => rw [mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, map_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg, map_neg]; exact neg_mem hx

theorem backward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idAt D (· = v)) (h : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) : s ∈ idV (dI D) v := by
  have hs1 : infPart D s = 0 := hs.1
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    rw [RingHom.map_mul, hs1, zero_mul]
  have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
    Conductor.idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
  obtain ⟨x, u, hu, e⟩ := Conductor.approx (finPart D s)
  have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
    have := Conductor.idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hx : TrInt D x := fun o => by
    have h1 := h _ (Conductor.lift_mem v o)
    have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
        (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Conductor.psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc,
      mul_comm (finPart D s), hz, e, add_mul, Conductor.chi_add,
      Conductor.chi_int hψ (Conductor.mul_mem_int hu (Conductor.tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
    exact (Conductor.chi_rat hψ _).1 h1
  have hfin : finPart D s = singleV D.host.F v 1 ⊗ₜ[D.host.F] x +
      (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u := by
    rw [← hz, e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [eq_lift hs1, hfin, map_add]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hε, fun w hw => Conductor.ev_ne hw, x, (mem_dI_iff x).2 hx,
    lift_tmul _ _⟩) (lift_int_mem v hε hu)

theorem idV_dI_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D),
    ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 :=
  fun _ _ hψ v _ hs => ⟨fun h => forward hψ v h, backward hψ v hs⟩

end GlobalTheory.SeeSaw.DiffDual

end
