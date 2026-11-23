import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstDerivativeAtNormalSet

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section supp

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
  have htop : ∀ (v : ℂ) (p q : Fin (2 * r + k + 1)),
      QuantumDeterminants.Top (Q.EH k r) v p q (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro v p q
    funext x
    simp only [QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
    exact eabH_zero p q x
  have hfold : ∀ L : List ((Q.Mx k r → E) → Q.Mx k r → E), (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) →
      L.foldr (fun T h => T h) (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons T L ih =>
      intro hT
      simp only [List.foldr_cons]
      rw [ih (fun T' h' => hT T' (by simp [h']))]
      exact hT T (by simp)
  funext x
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hfold _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact htop _ _ _)]
  simp

theorem AAop_zero' (m : ℕ) (hm : m ≤ r) (u : ℂ) (g : Q.Mx k r) :
    C3.AAop k r m hm u (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero' (m : ℕ) (hm : m ≤ r) (ell : ℂ) (g : Q.Mx k r) :
    C3.AAvop k r m hm ell (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAvop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero_near (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) {V : Set (Q.Mx k r)} (hV : IsOpen V) (hf : ∀ x ∈ V, x ∈ B.GV k r → f x = 0)
    (g : B.Mat k r) (hg : g ∈ V) (hgG : g ∈ B.GV k r) : D.vLet k r z z' j hj l e f g = 0 := by
  have hgl : g ∈ Q.Glev k r 0 ∩ V := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg⟩
  have hloc : ∀ x ∈ Q.Glev k r 0 ∩ V, f x = (fun _ : Q.Mx k r => (0 : E)) x := fun x hx => hf x hx.2 hx.1.1
  unfold D.vLet
  split_ifs
  · rfl
  · rw [AAop_loc hV _ _ _ f _ hloc g hgl, AAop_zero', smul_zero]
  · rw [AAvop_loc hV _ _ _ f _ hloc g hgl, AAvop_zero', smul_zero]

theorem uwG_supp (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (R : ℝ)
    (hR : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F j hj w e g ≠ 0 → B.gN g ≤ R
  | [], _, g, hg, hne => hR g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hgt
    push Not at hgt
    apply hne
    show D.vLet k r z z' j hj l (e 0) (D.uwG k r z z' F j hj w fun a => e a.succ) g = 0
    refine vLet_zero_near z z' j hj l (e 0) _ (V := {x | R < B.gN x})
      (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous) (fun x hx hxG => ?_) g hgt hg
    by_contra h0
    exact absurd (uwG_supp z z' F R hR j hj w _ x hxG h0) (not_le.2 hx)

theorem contOn_of_loc {f : B.Mat k r → E} {S : Set (B.Mat k r)}
    (h : ∀ x ∈ S, x ∈ B.GV k r → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) f x) : ContinuousOn f {x | x ∈ B.GV k r ∧ x ∈ S} := by
  intro x hx
  obtain ⟨U, f', hU, hxU, hf', he⟩ := h x hx.2 hx.1
  have hc : ContinuousWithinAt f' {x | x ∈ B.GV k r ∧ x ∈ S} x :=
    ((hf'.continuousOn).continuousAt (hU.mem_nhds hxU)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (he x hxU hx.1)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with y hyU hyS
  exact he y hyU hyS.1

end supp

end Formalism.FourierDecayAlt.P.PBG
