import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable local instance clmNACG : NormedAddCommGroup (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance clmNS : NormedSpace ℝ (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

lemma fderiv_apply_lin {f' : B.Mat k r → E} {U : Set (B.Mat k r)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 f' U) {g : B.Mat k r} (hg : g ∈ U) (A : B.Mat k r →L[ℝ] B.Mat k r) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f' y (A y)) g ∧
    ∀ V, fderiv ℝ (fun y => fderiv ℝ f' y (A y)) g V =
      fderiv ℝ f' g (A V) + fderiv ℝ (fderiv ℝ f') g V (A g) := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f' y) U :=
    hc.fderiv_of_isOpen hU (by first | norm_num | rfl | simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f') g :=
    (h1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hg)
  have hA : DifferentiableAt ℝ (fun y => A y) g := A.differentiableAt
  refine ⟨hd.clm_apply hA, fun V => ?_⟩
  have key := (hd.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  exact (congrArg (fun L => L V) key).trans rfl

lemma swap1 {X Y : B.Mat k r} (hX : B.inLie k r X) (hY : B.inLie k r Y) {h : B.Mat k r → E}
    (hh : B.CkOn 2 (B.GV k r) h) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Dx (false, X) (Dx (true, Y) h) g = Dx (true, Y) (Dx (false, X) h) g := by
  have hdx : ∀ (x : Bool × B.Mat k r), B.inLie k r x.2 → ∀ {f f' : B.Mat k r → E} {U : Set (B.Mat k r)},
      IsOpen U → (∀ y ∈ U, y ∈ B.GV k r → f y = f' y) → ∀ y ∈ U, y ∈ B.GV k r →
      DifferentiableAt ℝ f' y → Dx x f y = fderiv ℝ f' y (dirL x y) := by
    intro x hx f f' U hU hff y hyU hy hd
    rw [Dx_eq, dirL_apply]
    exact (Dx_hasDerivAt hx hU hyU hy hd hff).deriv
  obtain ⟨U, h', hU, hgU, hc, heq⟩ := hh g hg
  have hc2 : ContDiffOn ℝ 2 h' U := by exact_mod_cast hc
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ h' y := fun y hy =>
    (hc2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  obtain ⟨hdL, hfL⟩ := fderiv_apply_lin hU hc2 hgU (dirL (true, Y))
  obtain ⟨hdR, hfR⟩ := fderiv_apply_lin hU hc2 hgU (dirL (false, X))
  have e1 : Dx (false, X) (Dx (true, Y) h) g =
      Dx (false, X) (fun y => fderiv ℝ h' y (dirL (true, Y) y)) g :=
    Dx_congr_loc (x := (false, X)) hX hU
      (fun y hy hyU => hdx (true, Y) hY hU heq y hyU hy (hdiff y hyU)) g hg hgU
  have e2 : Dx (true, Y) (Dx (false, X) h) g =
      Dx (true, Y) (fun y => fderiv ℝ h' y (dirL (false, X) y)) g :=
    Dx_congr_loc (x := (true, Y)) hY hU
      (fun y hy hyU => hdx (false, X) hX hU heq y hyU hy (hdiff y hyU)) g hg hgU
  rw [e1, e2, hdx (false, X) hX hU (fun _ _ _ => rfl) g hgU hg hdL,
    hdx (true, Y) hY hU (fun _ _ _ => rfl) g hgU hg hdR, hfL, hfR]
  have hsymm : IsSymmSndFDerivAt ℝ h' g :=
    (hc2.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt (by simp)
  rw [show dirL (true, Y) (dirL (false, X) g) = dirL (false, X) (dirL (true, Y) g) by
      simp [dirL_apply, dirv, mul_assoc]]
  congr 1
  exact hsymm _ _

lemma ckDw {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → E} {m n : ℕ}
    (hf : B.CkOn (n : ℕ∞) (B.GV k r) f) (hmn : m + w.length ≤ n) : B.CkOn (m : ℕ∞) (B.GV k r) (Dw w f) := by
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw hw (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono (by exact_mod_cast hmn) hf)

lemma len_wL (u : List (B.Mat k r)) : (wL u).length = u.length := by
  simp [wL]

lemma len_wR (v : List (B.Mat k r)) : (wR v).length = v.length := by
  simp [wR]

lemma lie_wL {u : List (B.Mat k r)} (hu : ∀ X ∈ u, B.inLie k r X) : ∀ x ∈ wL u, B.inLie k r x.2 := by
  intro x hx
  simp only [wL, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hu X hX

lemma lie_wR {v : List (B.Mat k r)} (hv : ∀ X ∈ v, B.inLie k r X) : ∀ x ∈ wR v, B.inLie k r x.2 := by
  intro x hx
  simp only [wR, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hv X hX

lemma moveR {X : B.Mat k r} (hX : B.inLie k r X) : ∀ (u : List (B.Mat k r)), (∀ Y ∈ u, B.inLie k r Y) →
    ∀ {h : B.Mat k r → E}, B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h →
    ∀ g ∈ B.GV k r, Dx (false, X) (Dw (wL u) h) g = Dw (wL u) (Dx (false, X) h) g
  | [], _, _, _, _, _ => rfl
  | Y :: u, hu, h, hh, g, hg => by
    have hY : B.inLie k r Y := hu Y (by simp)
    have hu' : ∀ Z ∈ u, B.inLie k r Z := fun Z hZ => hu Z (by simp [hZ])
    show Dx (false, X) (Dx (true, Y) (Dw (wL u) h)) g = Dx (true, Y) (Dw (wL u) (Dx (false, X) h)) g
    have h2 : B.CkOn ((2 : ℕ) : ℕ∞) (B.GV k r) (Dw (wL u) h) :=
      ckDw (lie_wL hu') hh (by rw [len_wL]; simp; omega)
    rw [swap1 hX hY (by exact_mod_cast h2) hg]
    have hh' : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h :=
      sCkOn_mono (by exact_mod_cast (by simp : u.length + 1 ≤ (Y :: u).length + 1)) hh
    exact Dx_congr (x := (true, Y)) hY (moveR hX u hu' hh') g hg

lemma rightRegularAction_list_dLR_eq_append {f : B.Mat k r → E} {m : ℕ} (hf : B.CkOn (m : ℕ∞) (B.GV k r) f) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → u.length + v.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, B.Rw w (B.dLR u v f) g = B.dLR u (w ++ v) f g
  | [], _, _, _, _ => rfl
  | X :: w, hw, hm, g, hg => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have hm' : u.length + v.length + w.length ≤ m := by simp at hm; omega
    have e1 : ∀ F : B.Mat k r → E, Formalism.REAL.RdV X F = Dx (false, X) F := fun F => by simp [Dx]
    show Formalism.REAL.RdV X (B.Rw w (B.dLR u v f)) g = B.dLR u (X :: (w ++ v)) f g
    rw [e1, Dx_congr (x := (false, X)) hX (rightRegularAction_list_dLR_eq_append hf u v hu hv w hw' hm') g hg]
    simp only [dLR_eq, Dw_append, Dw_wR]
    have hck : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) (B.Rw (w ++ v) f) := by
      rw [← Dw_wR]
      refine ckDw (lie_wR ?_) hf ?_
      · intro Z hZ
        rcases List.mem_append.mp hZ with h | h
        · exact hw' Z h
        · exact hv Z h
      · rw [len_wR, List.length_append]; simp at hm; omega
    rw [moveR hX u hu hck g hg]
    rfl

end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity

namespace PI.UnitaryGroupMassFormula.UsCost

theorem commLR : CommLR := by
  unfold CommLR
  intro k r E _ _ f m hf u v w hu hv hw hlen g hg
  exact GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append hf u v hu hv w hw hlen g hg

end PI.UnitaryGroupMassFormula.UsCost
