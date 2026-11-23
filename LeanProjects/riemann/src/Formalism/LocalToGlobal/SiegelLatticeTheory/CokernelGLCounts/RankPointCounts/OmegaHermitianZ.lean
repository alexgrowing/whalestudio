import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsotropicSpanOrthogonalAnisotropicVector

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')

theorem GZ_eq : GZ F.fvec F'.fvec = Zhat F F' := by
  ext a b; rfl

theorem GDl_eq (l : ℕ) : GDl F.fvec F'.fvec l = Dl F F' l := by
  unfold GDl Dl leadMinorE
  rw [GZ_eq]

theorem om_X' {y : (VS D).V} (hy : y ∈ F'.X) : (VS D).hT (Gom F.fvec F'.fvec) y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, ← fvec_cs F' i, om_pair, if_neg (Fin.castSucc_ne_last i), smul_zero]

theorem omega_hermitian_z : (VS D).hT (Gom F.fvec F'.fvec) F'.z = GDl F.fvec F'.fvec (D.R.rS + 1) := by
  rw [← fvec_last F', om_pair, if_pos rfl]

theorem f_om (a : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) =
      if a = Fin.last D.R.rS then star ((GZ F.fvec F'.fvec).adjugate (Fin.last _) (Fin.last _)) * -T else 0 := by
  unfold Gom
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hff]
  rw [Finset.sum_eq_single (Fin.last D.R.rS)]
  · by_cases ha : a = Fin.last D.R.rS
    · rw [if_pos ⟨ha, rfl⟩, if_pos ha]
    · rw [if_neg (fun h => ha h.1), if_neg ha, mul_zero]
  · intro b _ hb
    rw [if_neg (fun h => hb h.2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_om : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
    -T * (GDl F.fvec F'.fvec D.R.rS * star (GDl F.fvec F'.fvec D.R.rS)) := by
  have e : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
      ∑ a, (GZ F.fvec F'.fvec).adjugate (Fin.last _) a * (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) := by
    conv_lhs => arg 1; unfold Gom
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [e, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [f_om, if_pos rfl, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r']
    ring
  · intro b _ hb
    rw [f_om, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_uniq (hdet : GDl F.fvec F'.fvec (D.R.rS + 1) ≠ 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.fvec)) (hxX : ∀ y ∈ F'.X, (VS D).hT y x = 0) :
    ∃ c : D.host.E, x = c • Gom F.fvec F'.fvec := by
  set c : D.host.E := star ((VS D).hT x F'.z / GDl F.fvec F'.fvec (D.R.rS + 1)) with hc
  refine ⟨c, sub_eq_zero.1 (eq_zero_of_orth_of_det_ne_zero F.fvec F'.fvec hdet
    (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Gom_mem _ _))) fun b => ?_)⟩
  rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, om_pair]
  induction b using Fin.lastCases with
  | last =>
    rw [if_pos rfl, fvec_last, hc, star_star, div_mul_cancel₀ _ hdet, sub_self]
  | cast i =>
    rw [if_neg (Fin.castSucc_ne_last i), mul_zero, sub_zero, fvec_cs, hsw',
      hxX _ (Submodule.subset_span ⟨i, rfl⟩), star_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
