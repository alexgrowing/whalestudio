import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

namespace Formalism.L2.DIV.FunSharpTop

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

def reExp (f : List ℝ → ℝ) (l : List ℝ) : List ℝ := l.take 16 ++ f (l.take 16) :: l.drop 17

theorem reExp_eq {eps : ℝ} (Fm : FamP eps) (f : List ℝ → ℝ) (CH : ℝ) :
    reExp f (Fm.cOut ++ Fm.cMid CH) = Fm.cOut ++ Fm.cMid (f Fm.cOut) := rfl

def sharpThresholdTransform (K : TransportedAlt) : TransportedAlt := ⟨K.pre, K.t, K.mid, fun l => K.last (reExp K.mid l)⟩

theorem large_of_large_thresholds {eps : ℝ} {Fm : FamP eps} {K : TransportedAlt} {CH : ℝ} (h : Fm.Large (sharpThresholdTransform K) CH) :
    Fm.Large K (K.mid Fm.cOut) := by
  unfold FamP.Large at h ⊢
  obtain ⟨h1, -, h3, h4⟩ := h
  refine ⟨h1, trivial, fun c hc => ?_, fun c hc => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc'
    · exact le_rfl
    · exact h3 c (List.mem_cons_of_mem _ hc')
  · have e := h4 c hc
    have e2 : (sharpThresholdTransform K).last (Fm.cOut ++ Fm.cMid CH) = K.last (Fm.cOut ++ Fm.cMid (K.mid Fm.cOut)) := by
      show K.last (reExp K.mid (Fm.cOut ++ Fm.cMid CH)) = _
      rw [reExp_eq]
    rw [e2] at e
    exact e

theorem closed_atMid {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) :
    ∃ f : ℝ → List ℝ → ℝ, Closed 𝒞 fun {eps} Fm _ => P Fm (f eps Fm.cOut) := by
  classical
  unfold Closed at h
  obtain ⟨ε1, hε1, hK⟩ := h
  refine ⟨fun eps l => if hh : 0 < eps ∧ eps ≤ ε1 then (Classical.choose (hK eps hh.1 hh.2)).mid l else 0, ?_⟩
  unfold Closed
  refine ⟨ε1, hε1, fun eps he he1 => ⟨sharpThresholdTransform (Classical.choose (hK eps he he1)), fun Fm CH hC hL => ?_⟩⟩
  dsimp only
  rw [dif_pos ⟨he, he1⟩]
  exact Classical.choose_spec (hK eps he he1) Fm _ hC (large_of_large_thresholds hL)

theorem closed_largeE {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : ℝ → TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), Fm.Large (K0 eps) CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hK⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK'⟩ := hK eps he he1
  refine ⟨⟨max K.pre (K0 eps).pre, K.t, fun l => max (K.mid l) ((K0 eps).mid l),
    fun l => max (K.last l) ((K0 eps).last l)⟩, fun Fm CH hC hL => ?_⟩
  unfold FamP.Large at hL
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hA : Fm.Large K CH := by
    unfold FamP.Large
    exact ⟨fun c hc => le_trans (le_max_left _ _) (h1 c hc), trivial,
      fun c hc => le_trans (le_max_left _ _) (h3 c hc), fun c hc => le_trans (le_max_left _ _) (h4 c hc)⟩
  have hB : Fm.Large (K0 eps) CH := by
    unfold FamP.Large
    exact ⟨fun c hc => le_trans (le_max_right _ _) (h1 c hc), trivial,
      fun c hc => le_trans (le_max_right _ _) (h3 c hc), fun c hc => le_trans (le_max_right _ _) (h4 c hc)⟩
  exact h Fm CH hB (hK' Fm CH hC hA)

end Formalism.L2.DIV.FunSharpTop

end
