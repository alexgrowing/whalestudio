import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdND

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem main (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hΛ₂ : Submodule.IsLattice E Λ₂)
    (hSD : SD S Λ) (hSD₂ : SD S Λ₂) (hX : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hL' : ∀ y ∈ Λ, y ∈ orth S X → ∃ x ∈ Λ₂, x ∈ orth S X ∧ y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ X, n x = x) ∧ n z = z ∧
      (∀ x ∈ orth S X, n x - x ∈ X) ∧ (n : S.V → S.V) '' Λ₂ = Λ := by
  classical
  have hXo := X_le_orth S X hXiso
  obtain ⟨A, hAX, hA0, hAz, hAΛ⟩ :=
    stepB S X hXiso z hzX Λ Λ₂ hΛ₂ hSD₂ (fun x hx h => (hX x hx).1 h) hz hz₂ hL hy
  obtain ⟨g, hg, hgA⟩ := stepW S X hXiso A hAX hA0
  have hgX : ∀ x ∈ X, g x = x := fun x hx => by
    have e : g x = x + A ⟨x, hXo hx⟩ := hgA ⟨x, hXo hx⟩
    rw [e, hA0 ⟨x, hXo hx⟩ hx, add_zero]
  let Λ₃ : Submodule (𝓞 E) S.V := Λ₂.map ((g : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))
  have hmem₃ : ∀ x, x ∈ Λ₃ ↔ g.symm x ∈ Λ₂ := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨g.symm x, h, by simp⟩
  have hfg₃ : Λ₃.FG := hΛ₂.fg.map _
  have hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃ := fun u => by
    obtain ⟨d, hd, hdu⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ₂ hΛ₂ (g.symm u)
    refine ⟨d, hd, (hmem₃ _).2 ?_⟩
    rw [oSmul, map_smul, ← oSmul]
    exact hdu
  have hSD₃ : SD S Λ₃ := fun x => by
    rw [hmem₃, hSD₂]
    constructor
    · intro h y hy
      have := h (g.symm y) ((hmem₃ y).1 hy)
      rwa [← hg (g.symm y) (g.symm x), g.apply_symm_apply, g.apply_symm_apply] at this
    · intro h y hy
      rw [← hg y (g.symm x), g.apply_symm_apply]
      exact h (g y) ((hmem₃ _).2 (by simpa using hy))
  have hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ := fun x hx => by
    rw [hmem₃]
    constructor
    · intro h
      obtain ⟨l, rfl⟩ : ∃ l, g l = x := ⟨g.symm x, g.apply_symm_apply x⟩
      rw [g.symm_apply_apply] at h
      have hlo : l ∈ orth S X := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun x' hx' => by
        rw [← hg x' l, hgX x' hx']
        exact orth_X S hx hx'
      have e : g l = l + A ⟨l, hlo⟩ := hgA ⟨l, hlo⟩
      rw [e]
      exact hAΛ l hlo h
    · intro h
      obtain ⟨x₂, hx₂, hx₂o, hxx₂⟩ := hL' x h hx
      have hAx₂ := hAΛ x₂ hx₂o hx₂
      obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = x - (x₂ + A ⟨x₂, hx₂o⟩) := ⟨_, rfl⟩
      have hξX : ξ ∈ X := by
        have e : ξ = (x - x₂) - A ⟨x₂, hx₂o⟩ := by rw [hξ]; abel
        rw [e]
        exact X.sub_mem hxx₂ (hAX _)
      have hξΛ : ξ ∈ Λ := by rw [hξ]; exact Λ.sub_mem h hAx₂
      have hξΛ₂ : ξ ∈ Λ₂ := (hX ξ hξX).2 hξΛ
      have hlo : x₂ + ξ ∈ orth S X := (orth S X).add_mem hx₂o (hXo hξX)
      have e : g (x₂ + ξ) = x := by
        have h1 : g (x₂ + ξ) = (x₂ + ξ) + A ⟨x₂ + ξ, hlo⟩ := hgA ⟨x₂ + ξ, hlo⟩
        have h2 : A ⟨x₂ + ξ, hlo⟩ = A ⟨x₂, hx₂o⟩ + A ⟨ξ, hXo hξX⟩ := by
          rw [← map_add]
          rfl
        rw [h1, h2, hA0 ⟨ξ, hXo hξX⟩ hξX, add_zero, hξ]
        abel
      rw [← e, g.symm_apply_apply]
      exact Λ₂.add_mem hx₂ hξΛ₂
  obtain ⟨n₂, hn₂, hn₂o, hn₂img⟩ := stepD S X hXiso Λ Λ₃ hΛ hSD hfg₃ hfull₃ hSD₃ hM htr
  refine ⟨g.trans n₂, fun a b => ?_, fun x hx => ?_, ?_, fun x hx => ?_, ?_⟩
  · show S.hT (n₂ (g a)) (n₂ (g b)) = S.hT a b
    rw [hn₂, hg]
  · show n₂ (g x) = x
    rw [hgX x hx, hn₂o x (hXo hx)]
  · have e : g z = z + A ⟨z, hzX⟩ := hgA ⟨z, hzX⟩
    show n₂ (g z) = z
    rw [e, hAz, add_zero, hn₂o z hzX]
  · have e : g x = x + A ⟨x, hx⟩ := hgA ⟨x, hx⟩
    have ho : g x ∈ orth S X := by rw [e]; exact (orth S X).add_mem hx (hXo (hAX _))
    show n₂ (g x) - x ∈ X
    rw [hn₂o _ ho, e, add_sub_cancel_left]
    exact hAX _
  · have h3 : (g : S.V → S.V) '' (Λ₂ : Set S.V) = (Λ₃ : Set S.V) := by
      rw [Submodule.map_coe]
      rfl
    have e : ((g.trans n₂ : S.V ≃ₗ[E] S.V) : S.V → S.V) = n₂ ∘ g := rfl
    rw [e, Set.image_comp, h3, hn₂img]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
