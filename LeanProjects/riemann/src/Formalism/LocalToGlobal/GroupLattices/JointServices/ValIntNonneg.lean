import Formalism.LocalToGlobal.GroupLattices.JointServices
import Formalism.LocalToGlobal.GroupLattices.JointServices.VAddEqVw
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem perCol_lin (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (φ : D.what₂.Mu u) :
    ∃ f : D.what₂.Amb μ →ₗ[ℂ] ℂ, ∀ F, D.what₂.perCol u μ φ F = f F := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    refine ⟨((D.mem u).P.period ((D.mem u).P.lowerMap ((D.mem u).P.evz ((D.mem u).C.col ↑(D.eMu u φ))))).comp
      (D.eMt u).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_base_eq_PtilCol]
    rfl
  · refine ⟨((D.PTw u μ).period ((D.PTw u μ).lowerMap ((D.PTw u μ).evz
      ((D.chTw u μ).col (D.e0Tw u μ ↑(D.eMu u φ)))))).comp (D.eMtTw u μ).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_tie u μ h]
    rfl

theorem cutUpOfOTie : CutUpOfOTie := by
  intro D hO μ hU x hx hV
  obtain ⟨ι, hι, hιO⟩ := hO.int
  exact (cut_tensorUp_row (RowSide.sharp D) hO.ded ι hι hιO hO.aint μ (hO.form μ hU) x).2 ⟨hx, hV⟩

theorem perToVal2 : PerToVal2 := by
  intro D B hB u t hcut z s N h φ hφ F hF
  obtain ⟨s0, hOk⟩ := hB.ok
  have hV0 : B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F) ∈ D.what₂.V0 (B.I.tup t) := by
    refine ⟨B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F), ?_⟩
    have h1 := (hB.sharp.forms t).op_eq ((rV0 D B.A B.Ps B.ψs t).mulVec F)
    rw [level_operator_fixes_image hOk B.Ps B.ψs B.Zs t F] at h1
    exact h1
  have hgen := ((hB.sharp.Mtilde t).2 _).1 ((image_mem_nabla_iff hOk B.Ps B.ψs B.Zs t F).2 hF)
  obtain ⟨S, c, hS, hx0⟩ := hcut _ hgen hV0
  have key : ∀ φ ∈ Submodule.span (𝓞 D.what₂.LL) N, VGeq z s (B.Dc.Pt (B.I.wU u) t φ F) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      have hex : ∀ y : D.what₂.Amb (B.I.tup t), ∃ a : D.what₂.LL, y ∈ S →
          (D.what₂.embLL a = D.what₂.perCol u (B.I.tup t) (D.jN u (B.I.eNu u x)) y ∧ (a = 0 ∨ s ≤ (vAdd z a : ℝ))) := by
        intro y
        by_cases hy : y ∈ S
        · obtain ⟨a, ha⟩ := h x hx y (hS hy).1 (hS hy).2
          exact ⟨a, fun _ => ha⟩
        · exact ⟨0, fun h' => absurd h' hy⟩
      choose a ha using hex
      obtain ⟨f, hf⟩ := perCol_lin D u (B.I.tup t) (D.jN u (B.I.eNu u x))
      have heq : B.Dc.Pt (B.I.wU u) t x F = ∑ y ∈ S, ((c y : 𝓞 D.what₂.LL) : D.what₂.LL) * a y := by
        apply D.what₂.embLL.injective
        rw [hB.dcPt u t x F, hf]
        refine (congrArg f hx0).trans ?_
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [map_smul, smul_eq_mul, map_mul, (ha y hy).1, hf]
      rw [heq]
      exact VGeq.sum S _ fun y hy => VGeq.int_mul (c y) (ha y hy).2
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact VGeq.zero z s
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact hx.add hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact VGeq.int_mul a hx
  exact (key φ hφ).vw

theorem val2AllAtR : SecondLevelValuationAtRestricted := by
  intro D L B hB hcut h u Nu hNu z
  have hμ := hB.mu (D.plEq.symm z)
  rw [Equiv.apply_symm_apply] at hμ
  have h2 : ∀ μ, D.what₂.muAt (D.plEq.symm z) = μ → ∀ φ ∈ L.NuLat u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
        (y = 0 ∨ ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) ≤ (vAdd (D.plEq (D.plEq.symm z)) y : ℝ)) := by
    rintro μ rfl
    exact h u (D.plEq.symm z)
  have h3 := perToVal2 D B hB u (B.S1.μ z) (hcut _ (hμ ▸ used_muAt D (D.plEq.symm z))) z ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) (Nu : Set _)
    (fun x hx F hF1 hF0 => by
      have h4 := h2 _ hμ _ (hNu x hx) F hF1 hF0
      rw [Equiv.apply_symm_apply] at h4
      exact h4)
  rw [Submodule.span_eq] at h3
  exact h3

end Formalism.L2.G.ServJoint

end
