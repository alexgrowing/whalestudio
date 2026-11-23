import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmegaHermitianZ

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open SpanOmPf in

theorem spanOm_holds (D : Formalism.BasicNotions.D7) : SpanOm D := by
  intro T T' F F' hdet hG m hm
  set ω := Gom F.fvec F'.fvec with hω
  set Dd := GDl F.fvec F'.fvec (D.R.rS + 1) with hDd
  set Dr := GDl F.fvec F'.fvec D.R.rS with hDr
  have hD : Dd ≠ 0 := by rw [hDd, GDl_top', SpanOmPf.GZ_eq]; exact hdet
  have hG' : Dd * star Dd - T * T' * (Dr * star Dr) ≠ 0 := by
    rw [hDd, hDr, SpanOmPf.GDl_eq, SpanOmPf.GDl_eq]; exact hG
  set W0 := orth (VS D) (F.Xplus ⊔ F'.Xplus) with hW0
  set U := F'.X ⊔ W0 ⊔ Submodule.span D.host.E {F'.z, ω} with hU
  have key : ∀ u ∈ orth (VS D) U, u ∈ F'.X := by
    intro u hu
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hu
    have h1 : ∀ y ∈ F'.X, (VS D).hT y u = 0 := fun y hy =>
      hu y (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    have h2 : ∀ w ∈ W0, (VS D).hT w u = 0 := fun w hw =>
      hu w (Submodule.mem_sup_left (Submodule.mem_sup_right hw))
    have h3 : (VS D).hT F'.z u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _)))
    have h4 : (VS D).hT ω u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hP : u ∈ F.Xplus ⊔ F'.Xplus :=
      BwdNA.mem_of_orth_orth (VS D) _ (fun w hw => by rw [SpanOmPf.hsw', h2 w hw, star_zero])
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hP
    obtain ⟨y', hy', s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hs
    have hxX : ∀ y0 ∈ F'.X, (VS D).hT y0 x = 0 := by
      intro y0 hy0
      have := h1 y0 hy0
      rw [map_add, map_add, SpanOmPf.iso_X F' hy0 hy', map_smul, SpanOmPf.isotropicSpan_orthogonal_anisotropicVector F' hy0, smul_zero, add_zero, add_zero] at this
      exact this
    obtain ⟨c, rfl⟩ := SpanOmPf.om_uniq F F' hD (by rw [← SpanOmPf.Xplus_eq]; exact hx) hxX
    have hzo : (VS D).hT F'.z ω = star Dd := by rw [SpanOmPf.hsw', SpanOmPf.omega_hermitian_z]
    have e3 : c * star Dd + β * -T' = 0 := by
      have := h3
      rw [map_add, map_add, map_smul, map_smul, hzo, SpanOmPf.z_orth_X F' hy', F'.z_norm, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have e4 : c * (-T * (Dr * star Dr)) + β * Dd = 0 := by
      have := h4
      rw [map_add, map_add, map_smul, map_smul, SpanOmPf.om_om, SpanOmPf.om_X' F F' hy', SpanOmPf.omega_hermitian_z, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have hc : c = 0 := by
      have hcG : c * (Dd * star Dd - T * T' * (Dr * star Dr)) = 0 := by
        linear_combination Dd * e3 + T' * e4
      exact (mul_eq_zero.1 hcG).resolve_right hG'
    have hβ : β = 0 := by
      rw [hc] at e4
      have : β * Dd = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_right hD
    rw [hc, hβ, zero_smul, zero_smul, add_zero, zero_add]
    exact hy'
  have hmU : m ∈ U := BwdNA.mem_of_orth_orth (VS D) U (fun u hu => by
    rw [SpanOmPf.hsw', (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm u (key u hu), star_zero])
  obtain ⟨y, hy, s, hs, rfl⟩ := Submodule.mem_sup.1 hmU
  obtain ⟨x', hx', w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hs
  exact ⟨x', hx', w, hw, a, b, by abel⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
