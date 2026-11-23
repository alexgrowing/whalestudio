import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem injective_of_scalars {ι V W : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S)
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (h : ∀ σ, S σ ≠ ⊥ → ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f) :
    Function.Injective A := by
  classical
  have h' : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f := by
    intro σ
    by_cases hσ : S σ = ⊥
    · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
      rw [hσ, Submodule.mem_bot] at hf
      simp [hf]
    · exact h σ hσ
  choose c hc0 hc using h'
  let _ := hS.chooseDecomposition
  have key : ∀ v : V, ∀ k, ((DirectSum.decompose S (B (A v)) k : S k) : V) =
      c k • ((DirectSum.decompose S v k : S k) : V) := by
    intro v
    induction v using DirectSum.Decomposition.inductionOn S with
    | zero => intro k; simp
    | @homogeneous i m =>
      intro k
      have hm : B (A (m : V)) ∈ S i := by
        rw [hc i _ m.2]; exact (S i).smul_mem _ m.2
      by_cases hik : i = k
      · subst hik
        rw [DirectSum.decompose_of_mem_same S hm, DirectSum.decompose_of_mem_same S m.2, hc i _ m.2]
      · rw [DirectSum.decompose_of_mem_ne S hm hik, DirectSum.decompose_of_mem_ne S m.2 hik, smul_zero]
    | add a b ha hb =>
      intro k
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, smul_add, ha k, hb k]
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hz : DirectSum.decompose S v = 0 := by
    ext k
    have := key v k
    rw [hv, map_zero, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 k)
  exact (DirectSum.decompose S).injective (by rw [hz, DirectSum.decompose_zero])

theorem thetaT_injective_of_onto {R : Ranks} (D : Rows.Data R) (μ : D.Tup) (j : ℕ)
    (h : Function.Surjective (D.thetaP μ j)) : Function.Injective (D.thetaT μ j) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := h y
  have h1 : inner ℂ x (D.thetaT μ j (D.thetaP μ j x)) = inner ℂ (D.thetaP μ j x) (D.thetaP μ j x) := by
    unfold Rows.Data.thetaT
    exact LinearMap.adjoint_inner_right _ _ _
  rw [hy, inner_zero_right] at h1
  exact inner_self_eq_zero.mp h1.symm

theorem finrank_Zj_of_injective {R : Ranks} (D : Rows.Data R) (μ : D.Tup) (j : ℕ)
    (h : Function.Injective (D.thetaT μ j)) :
    Module.finrank ℂ (D.Zj μ j) = Module.finrank ℂ (D.Mj j) :=
  LinearMap.finrank_range_of_inj h

theorem finrank_Mj {D : D7} (X : DivX D) (j : ℕ) (hr : (X.MjH j).rank = D.what₂.D0) :
    Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  have hb := X.jM_basis j
  have h1 : Module.finrank ℂ (D.what₂.Mj j) = Fintype.card (X.MjH j).ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hb.1 (by rw [hb.2]))
  have h2 : (X.MjH j).rank = Fintype.card (X.MjH j).ι := by
    unfold HLat.rank Formalism.HN.rkK
    rw [(X.MjH_good j).2.2, finrank_top]
    exact Module.finrank_eq_card_basis (X.MjH j).b
  rw [h1, ← h2, hr]

theorem finrank_of_lines {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S) (h1 : ∀ σ, Module.finrank ℂ (S σ) = 1) :
    Module.finrank ℂ V = Fintype.card ι := by
  have : ∀ σ, Module.Finite ℂ (S σ) := fun σ => Module.finite_of_finrank_pos (by rw [h1 σ]; exact one_pos)
  have e : (DirectSum ι fun σ => S σ) ≃ₗ[ℂ] V := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hS
  rw [← e.finrank_eq, Module.finrank_directSum]
  simp [h1]

theorem finrank_Mj_of_isot {R : Ranks} (D : Rows.Data R) (hI : Rows.IsotInternal D) (hR : Rows.IsotRank D)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ R.m) : Module.finrank ℂ (D.Mj j) = D.D0 := by
  have e : (DirectSum D.FT fun π => D.isot j π) ≃ₗ[ℂ] D.Mj j :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (D.isot j)) (hI j h1 h2)
  rw [← e.finrank_eq, Module.finrank_directSum]
  simp only [hR j h1 h2, Rows.Data.nRows0]
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.ft0), Fintype.card_fin]

end Formalism.MainNotions.J

end
