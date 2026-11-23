import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnipotentRadicalActionFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_pWpR : Continuous (PI.LevelKSplit.W.NC.pWp R σ J P) := by
  show Continuous fun x => PI.LevelKSplit.W.NC.pWp R σ J P x
  unfold PI.LevelKSplit.W.NC.pWp
  refine (continuous_id.sub ?_).sub ?_ <;>
  refine continuous_finset_sum _ fun a _ => ?_ <;>
  exact (PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := continuous_const) (hv := continuous_id)).smul continuous_const

theorem continuous_yH : Continuous (PI.LevelKSplit.W.NC.yH R σ J P) := by
  refine continuous_pi fun a => ?_
  exact (continuous_pWpR P).comp (PI.VolSemiDirect.W.Md.continuous_linear_action _ σ J (hg := continuous_id) (hv := continuous_const))

theorem continuous_sL_apply (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by
  have hh : ∀ {u w : X → Fin M → R ⊗[F] E}, Continuous u → Continuous w →
      Continuous fun x => (PI.VolSemiDirect.W.datR R σ J P T).h (u x) (w x) :=
    fun hu hw => PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := hu) (hv := hw)
  simp only [sL, uv, cf, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply, PI.VolSemiDirect.W.PG.Dat.hL,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine (continuous_const.add (continuous_finset_sum _ fun a _ => ?_)).sub
    (continuous_finset_sum _ fun b _ => ?_)
  · exact (hh continuous_const continuous_const).smul (((continuous_apply a).comp hy).add
      (continuous_finset_sum _ fun b _ => ((continuous_const.mul
        (hh ((continuous_apply b).comp hy) ((continuous_apply a).comp hy))).neg).smul continuous_const))
  · exact (hh ((continuous_apply b).comp hy) continuous_const).smul continuous_const

theorem continuous_sLmat (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) :
    Continuous fun x => LinearMap.toMatrix' (sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (continuous_sL_apply P T half hy _)

end Cont

end PI.LevelKSplit.W.NCH
