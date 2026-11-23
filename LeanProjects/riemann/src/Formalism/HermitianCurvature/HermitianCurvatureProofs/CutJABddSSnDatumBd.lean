import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pair

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂]

theorem ssn_ckOn_subset {m : ℕ∞} {UU UU' : Set (Mat k r)} {f : Mat k r → E₁} (h : CkOn m UU f) (hs : UU' ⊆ UU) :
    CkOn m UU' f := fun g hg => h g (hs hg)

theorem ssn_ckOn_pair {m : ℕ∞} {UU : Set (Mat k r)} {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn m UU f₁) (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => (f₁ g, f₂ g)) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => (f₁' g, f₂' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).prodMk (hc₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show (f₁ g, f₂ g) = (f₁' g, f₂' g)
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

theorem ssn_Dw_pair {U : Set (Mat k r)} (hU : IsOpen U) {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn ⊤ (U ∩ GV k r) f₁) (h₂ : CkOn ⊤ (U ∩ GV k r) f₂) :
    ∀ w : List (Bool × Mat k r), (∀ x ∈ w, inLie k r x.2) → ∀ g ∈ GV k r, g ∈ U →
      Dw w (fun g => (f₁ g, f₂ g)) g = (Dw w f₁ g, Dw w f₂ g) := by
  intro w
  induction w with
  | nil => intro _ g _ _; rfl
  | cons x w ih =>
    intro hw g hg hgU
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    show Dx x (Dw w (fun g => (f₁ g, f₂ g))) g = (Dx x (Dw w f₁) g, Dx x (Dw w f₂) g)
    rw [Dx_congr_loc hx hU (f₂ := fun g => (Dw w f₁ g, Dw w f₂ g)) (fun g hg hgU => ih hw' g hg hgU) g hg hgU]
    have c₁ : CkOn 1 (U ∩ GV k r) (Dw w f₁) := CkOn_Dw hw' (sCkOn_mono le_top h₁)
    have c₂ : CkOn 1 (U ∩ GV k r) (Dw w f₂) := CkOn_Dw hw' (sCkOn_mono le_top h₂)
    have d₁ := CkOn_diff hx c₁ ⟨hgU, hg⟩ hg
    have d₂ := CkOn_diff hx c₂ ⟨hgU, hg⟩ hg
    rw [Dx_eq]
    exact (d₁.prodMk d₂).deriv

end pair

theorem datumBd_of_chain (hCh : SSn.ChainBd) : DatumBd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v Bg a a' ι Ψ hBg hD hΨ
  intro ε hε m
  set U : Set (B.Mat S.G.k S.G.r) := {g | ε / 2 < GfP S T v g} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  set K : Set (B.Mat S.G.k S.G.r) := {g | g ∈ B.GV S.G.k S.G.r ∧ ε ≤ GfP S T v g} with hKdef
  have hUG : U ∩ B.GV S.G.k S.G.r ⊆ B.GPos (T v).base := fun g hg =>
    ⟨hg.2, lt_trans (by linarith) hg.1⟩
  have hKU : K ⊆ U := fun g hg => show ε / 2 < GfP S T v g by linarith [hg.2]
  have hKG : K ⊆ B.GV S.G.k S.G.r := fun g hg => hg.1
  set F : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      B.Mat S.G.k S.G.r := fun g => (a g, (a' g, ι g)) with hFdef
  have cka : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a := ssn_ckOn_subset hD.1 hUG
  have cka' : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a' := ssn_ckOn_subset hD.2.1 hUG
  have ckι : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) ι := ssn_ckOn_subset hD.2.2.1 hUG
  have ckF : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) F := ssn_ckOn_pair cka (ssn_ckOn_pair cka' ckι)
  have hFb : ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r), (∀ X ∈ u, unitLie S.G.k S.G.r X) →
      (∀ X ∈ w, unitLie S.G.k S.G.r X) → u.length + w.length ≤ m → ∀ g ∈ K,
        ‖dLR u w F g‖ ≤ C * gN g ^ (Bg * m) := by
    intro m
    obtain ⟨C₁, h₁⟩ := hD.2.2.2.2.1 ε hε m
    obtain ⟨C₂, h₂⟩ := hD.2.2.2.2.2.1 ε hε m
    obtain ⟨C₃, h₃⟩ := hD.2.2.2.2.2.2.1 ε hε m
    refine ⟨C₁ + C₂ + C₃, fun u w hu hw hl g hg => ?_⟩
    have hlie := lie_LR (unit_lie hu) (unit_lie hw)
    have e1 : dLR u w F g = (dLR u w a g, (dLR u w a' g, dLR u w ι g)) := by
      rw [dLR_eq, dLR_eq, dLR_eq, dLR_eq]
      rw [ssn_Dw_pair hUo cka (ssn_ckOn_pair cka' ckι) _ hlie g hg.1 (hKU hg),
        ssn_Dw_pair hUo cka' ckι _ hlie g hg.1 (hKU hg)]
    rw [e1]
    have b₁ := h₁ u w hu hw hl g hg.1 hg.2
    have b₂ := h₂ u w hu hw hl g hg.1 hg.2
    have b₃ := h₃ u w hu hw hl g hg.1 hg.2
    calc ‖(dLR u w a g, (dLR u w a' g, dLR u w ι g))‖
        ≤ ‖dLR u w a g‖ + (‖dLR u w a' g‖ + ‖dLR u w ι g‖) :=
          (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (by positivity),
            (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (norm_nonneg _),
              le_add_of_nonneg_left (norm_nonneg _)⟩).trans (le_add_of_nonneg_left (norm_nonneg _))⟩)
      _ ≤ C₁ * gN g ^ (Bg * m) + (C₂ * gN g ^ (Bg * m) + C₃ * gN g ^ (Bg * m)) := by
          linarith
      _ = (C₁ + C₂ + C₃) * gN g ^ (Bg * m) := by ring
  obtain ⟨C, hC⟩ := hCh S.G.k S.G.r _ _ (fun x => Ψ x.1 x.2.1 x.2.2) hΨ F U K hUo ckF hKU hKG Bg hBg hFb m
  refine ⟨C, fun u w hu hw hl g hg hεg => ?_⟩
  have hgK : g ∈ K := ⟨hg, hεg⟩
  have hO : IsOpen {g : B.Mat S.G.k S.G.r | 0 < GfP S T v g} :=
    isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  have hlie := lie_LR (unit_lie hu) (unit_lie hw)
  have e : dLR u w (datumCoef S T v Ψ a a' ι) g = dLR u w (fun g => (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r => Ψ x.1 x.2.1 x.2.2) (F g)) g := by
    rw [dLR_eq, dLR_eq]
    refine Dw_congr_loc hlie hO (fun g' hg' hg'O => ?_) g hg (show 0 < GfP S T v g by linarith)
    exact datumCoef_pos S T v a a' ι Ψ ⟨hg', hg'O⟩
  rw [e]
  exact hC u w hu hw hl g hgK

end Formalism.FourierDecayAlt.P.CutMP.JA
