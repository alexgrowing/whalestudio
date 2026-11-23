import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtRightDerivativeCurve

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Ent

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothG_of_sf {a : Mx k ρ → ℂ}
    (h : SmoothFam k ρ (Fin.last ρ) (Set.univ : Set (Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) (fun _ g => a g)) : SmoothG k ρ a := by
  intro y₀ hy₀
  obtain ⟨U, F, hU, hxU, hF, hfF⟩ := h ((0 : Fin ρ → ℂ), Matrix.of y₀) (Set.mem_univ _) hy₀
  have hm : Continuous fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    continuous_const.prodMk continuous_id
  have hmd : ContDiff ℝ ∞ fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) ⁻¹' U,
    fun y => F ((0 : Fin ρ → ℂ), Matrix.of y), hU.preimage hm, hxU, hF.comp hmd.contDiffOn (fun y hy => hy),
    fun y hy hG => hfF _ hy hG⟩

theorem smoothG_yv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => yv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_yv z j)

theorem smoothG_ybv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => ybv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_ybv z j)

theorem parOK_EH (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (EH k ρ (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) :=
  parOK_congr (parOK_add (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).1))
    (parOK_csmul Complex.I
      (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).2)))) (fun f g => rfl)

theorem parOK_Top (u : ℂ) (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (Top (EH k ρ) u (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) := by
  by_cases hab : posL k ρ (Fin.last ρ) a = posL k ρ (Fin.last ρ) b
  · exact parOK_congr (parOK_add (parOK_csmul u parOK_id) (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])
  · exact parOK_congr (parOK_add parOK_zero (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])

theorem parOK_qminor {t : ℕ} (a b : Fin t → Fin (mdim k ρ (Fin.last ρ))) (u : ℂ) :
    ParOK k ρ (E := E) (qminorOp (EH k ρ) (posL k ρ (Fin.last ρ) ∘ a) (posL k ρ (Fin.last ρ) ∘ b) u) := by
  have key : ∀ σ : Equiv.Perm (Fin t), ParOK k ρ (E := E) (fun f g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k ρ) (u - ((j : ℕ) : ℂ)) ((posL k ρ (Fin.last ρ) ∘ a) (σ j))
          ((posL k ρ (Fin.last ρ) ∘ b) j)).foldr (fun T h => T h) f g)) := by
    intro σ
    refine parOK_csmul _ (parOK_foldr _ ?_)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact parOK_Top _ _ _
  refine parOK_congr (parOK_sum Finset.univ (fun σ _ => key σ)) (fun f g => ?_)
  simp [qminorOp, Finset.sum_apply]

theorem parOK_chatL (u : ℂ) (a β : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) :
    ParOK k ρ (E := E) (chatL (EH k ρ) (posL k ρ (Fin.last ρ)) u a β) := by
  refine parOK_congr (parOK_sum Finset.univ fun i' _ => parOK_sum Finset.univ fun j' _ =>
    parOK_smulG (smoothG_mul (smoothG_mul (smoothG_const _) (hβ i')) (ha j')) (parOK_qminor _ _ _))
    (fun f g => rfl)

theorem parOK_chat2L (u : ℂ) (a a' β β' : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (ha' : ∀ j, SmoothG k ρ (fun g => a' g j))
    (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) (hβ' : ∀ j, SmoothG k ρ (fun g => β' g j)) :
    ParOK k ρ (E := E) (chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) u a a' β β') := by
  refine parOK_congr (parOK_sum Finset.univ fun i₁ _ => parOK_sum Finset.univ fun i₂ _ =>
    parOK_sum Finset.univ fun j₁ _ => parOK_sum Finset.univ fun j₂ _ => ?_) (fun f g => rfl)
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · refine parOK_congr (parOK_smulG (smoothG_mul (smoothG_mul
      (smoothG_const ((-1 : ℂ) ^ ((i₁ : ℕ) + (i₂ : ℕ) + (j₁ : ℕ) + (j₂ : ℕ))))
      (smoothG_sub (smoothG_mul (hβ i₁) (hβ' i₂)) (smoothG_mul (hβ i₂) (hβ' i₁))))
      (smoothG_sub (smoothG_mul (ha j₁) (ha' j₂)) (smoothG_mul (ha j₂) (ha' j₁)))) (parOK_qminor (skip2 i₁ i₂) (skip2 j₁ j₂) u))
      (fun f g => by simp only [if_pos hc])
  · exact parOK_congr parOK_zero (fun f g => by simp only [if_neg hc])

theorem parOK_tL (z z' : Fin (2 * ρ + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    ParOK k ρ (E := E) (tL k ρ z z' (Fin.last ρ) Y p q) := by
  fin_cases p <;> fin_cases q
  · show ParOK k ρ (capL k ρ (Fin.last ρ) (uC k ρ (Fin.last ρ) Y))
    exact parOK_qminor id id _
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_const _) (fun j => smoothG_ybv z j))
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y) (yv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _))
  · show ParOK k ρ (fun f g => -(chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (yv k ρ z (Fin.last ρ)) (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chat2L _ _ _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _)
      (fun j => smoothG_ybv z j) (fun j => smoothG_const _))

end Ent

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
