import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coefficient_vector_in_class : CVCC := by
  intro k r Wp Wq _ _ _ _ _ _ s Y A m F _ hF
  exact Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class k r _ A m F Y s hF

theorem coefficient_vector_congr : CVCongr := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F F₁ hF hF₁ heq g hg
  have hmono : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) G →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Set.univ ∩ B.GV k r) G := by
    intro G hG g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hG g₀ hg₀.2
    exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) Set.univ F F₁ Y isOpen_univ
    (hmono F hF) (hmono F₁ hF₁) (fun x hx => heq x hx.2) g ⟨trivial, hg⟩
  simp only [Pi.smul_apply]
  rw [h]

theorem cV_zero {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    Q.CV k r Y (0 : B.Mat k r → E) = 0 := by
  have hop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.Top (Q.EH k r) u a b (0 : B.Mat k r → E) = 0 := by
    intro u a b
    funext g
    simp [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV]
  have hfold : ∀ l : List ((B.Mat k r → E) → (B.Mat k r → E)), (∀ T ∈ l, T 0 = 0) →
      l.foldr (fun T h => T h) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons T l ih =>
      simp only [List.foldr_cons]
      rw [ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT'))]
      exact hl T List.mem_cons_self
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [hfold _ ?_, smul_zero]
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hop _ _ _

theorem coefficient_vector_support : CVSupp := by
  intro k r Wp Wq _ _ _ _ _ _ z z' c s Y F hF hsupp g hg hne
  by_contra hlt
  push_neg at hlt
  have hU : IsOpen {x | Gf k r z z' x < c} :=
    isOpen_lt (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z') continuous_const
  have hF0 : ∀ x ∈ {x | Gf k r z z' x < c} ∩ B.GV k r,
      F x = (0 : B.Mat k r → (Wq →L[ℂ] Wp)) x := by
    intro x hx
    by_contra hne'
    exact absurd (hsupp x hx.2 hne') (not_le.mpr hx.1)
  have hCk0 : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r)
      (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hCkF : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU', hgU, hcd, hfe⟩ := hF g₀ hg₀.2
    exact ⟨U, f', hU', hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) {x | Gf k r z z' x < c} F 0 Y hU
    hCkF hCk0 hF0 g ⟨hlt, hg⟩
  apply hne
  simp only [Pi.smul_apply]
  rw [h, cV_zero, Pi.zero_apply, smul_zero]

theorem coefficient_vector_smoothness : CVSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F hF
  have hadd : ∀ {f g : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) g →
      B.CkOn ⊤ (B.GV k r) (f + g) := by
    intro f g hf hg g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    obtain ⟨U2, f2, hU2, h2, hc2, he2⟩ := hg g₀ hg₀
    refine ⟨U1 ∩ U2, f1 + f2, hU1.inter hU2, ⟨h1, h2⟩,
      (hc1.mono Set.inter_subset_left).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro x hx hxG
    simp [he1 x hx.1 hxG, he2 x hx.2 hxG]
  have hsmul : ∀ (c : ℂ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f →
      B.CkOn ⊤ (B.GV k r) (c • f) := by
    intro c f hf g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    refine ⟨U1, c • f1, hU1, h1, hc1.const_smul c, ?_⟩
    intro x hx hxG
    simp [he1 x hx hxG]
  have hzero : B.CkOn ⊤ (B.GV k r) (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hrd : ∀ X : B.Mat k r, B.inLie k r X → ∀ {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.REAL.RdV X f) := by
    intro X hX f hf
    have h1 : B.CkOn ((⊤ : ℕ∞) + 1) (B.GV k r) f := by
      rw [top_add]
      exact hf
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX h1
  have hTop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)) {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f) := by
    intro u a b f hf
    have e : Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f = (if a = b then u • f else 0) +
        (Formalism.REAL.RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f +
          Complex.I • Formalism.REAL.RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f) := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> simp
    rw [e]
    refine hadd ?_ (hadd (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie1 _) hf) (hsmul _ (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie2 _) hf)))
    split_ifs
    · exact hsmul u hf
    · exact hzero
  have hfold : ∀ l : List ((B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp))),
      (∀ T ∈ l, ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (T f)) →
      ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (l.foldr (fun T h => T h) f) := by
    intro l hl f hf
    induction l with
    | nil => exact hf
    | cons T l ih =>
      simp only [List.foldr_cons]
      exact hl T List.mem_cons_self _ (ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT')))
  apply hsmul s
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_induction _ (fun f => B.CkOn ⊤ (B.GV k r) f) (fun a b ha hb => hadd ha hb) hzero ?_
  intro σ _
  apply hsmul
  refine hfold _ ?_ F hF
  intro T hT f hf
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hTop _ _ _ hf

end Formalism.FourierDecayAlt.P.CutMP.ER
