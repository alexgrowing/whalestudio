import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjScale

open Classical in

noncomputable def forestLift {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (w : Fin r → Fin r → G) (j : Fin r) : G :=
  if h : ∃ i, Ed i j then forestLift Ed hlt w (Classical.choose h) * w (Classical.choose h) j else 1
termination_by j.val
decreasing_by all_goals (try simp_wf); exact hlt _ _ (Classical.choose_spec h)

theorem forestLift_edge {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (huniq : ∀ i i' j, Ed i j → Ed i' j → i = i') (w : Fin r → Fin r → G) {i j : Fin r} (h : Ed i j) :
    (forestLift Ed hlt w i)⁻¹ * forestLift Ed hlt w j = w i j := by
  have hex : ∃ i, Ed i j := ⟨i, h⟩
  have hc : Classical.choose hex = i := huniq _ _ _ (Classical.choose_spec hex) h
  have e : forestLift Ed hlt w j = forestLift Ed hlt w i * w i j := by
    rw [forestLift, dif_pos hex, hc]
  rw [e, inv_mul_cancel_left]

theorem symEdge_lt {r : ℕ} (ρ k : ℕ) : ∀ i j : Fin r, symEdge ρ k i j → i < j := by
  intro i j h
  show i.val < j.val
  unfold symEdge at h
  omega

theorem symEdge_uniq {r : ℕ} (ρ k : ℕ) : ∀ i i' j : Fin r, symEdge ρ k i j → symEdge ρ k i' j → i = i' := by
  intro i i' j h h'
  apply Fin.ext
  unfold symEdge at h h'
  omega

theorem scale_conj : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  intro κf _ _ hF r ρ k ψ' ψ0 h1 h0 a
  let _ : Field κf := hF.toField
  have := Fintype.ofFinite κf
  have hprim : ψ0.IsPrimitive := AddChar.IsPrimitive.of_ne_one h0
  have hinj : Function.Injective ψ0.mulShift := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hbij : Function.Bijective ψ0.mulShift := by
    classical
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    rw [← hc]
    exact AddChar.mulShift_zero ψ0
  let w : Fin r → Fin r → κfˣ := fun i j => Units.mk0 c hc0 * a i j
  refine ⟨forestLift (symEdge ρ k) (symEdge_lt ρ k) w, fun u _ => ?_⟩
  rw [← hc, AddChar.mulShift_apply]
  congr 1
  unfold edgeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [diagGL_conj_apply]
    have e := congrArg Units.val (forestLift_edge (symEdge ρ k) (symEdge_lt ρ k) (symEdge_uniq ρ k) w h)
    rw [Units.val_mul] at e
    have e2 : (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
        ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf) = c * (a i j : κf) := by
      rw [e]; rfl
    symm
    calc (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) * u.val i j *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)
        = ((((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)) * u.val i j := by ring
      _ = c * ((a i j : κf) * u.val i j) := by rw [e2]; ring
  · rw [mul_zero]

end GlobalTheory.SeeConjScale
