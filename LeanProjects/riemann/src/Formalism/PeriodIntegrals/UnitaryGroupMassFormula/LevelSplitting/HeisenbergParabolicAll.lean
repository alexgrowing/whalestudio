import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergCocycleMemCentre
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCHeisC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W NumberField IsDedekindDomain
open scoped TensorProduct

theorem heisenberg_parabolic (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    PI.LevelKSplit.W.NC.HeisP F E σ M J := by
  intro hJ hσσ r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp (R := Af F) hσσ hJ hP
  have hh : Half (datR (Af F) σ J P T) (algebraMap F (Af F ⊗[F] E) (1 / 2)) := by
    refine ⟨?_, ?_⟩
    · rw [← map_add, add_halves, map_one]
    · show (Algebra.TensorProduct.map (AlgHom.id F (Af F)) σ) (algebraMap F (Af F ⊗[F] E) (1 / 2)) =
        algebraMap F (Af F ⊗[F] E) (1 / 2)
      exact AlgHom.commutes _ _
  have hcy : Continuous fun y : Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P =>
      fun a => (y a : Fin M → Af F ⊗[F] E) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  refine ⟨fun y => sHG hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2),
    ?_, continuous_yH P, fun y => sHG_mem hJ H hh _, fun g hg => ?_, fun y z hz a => ?_,
    centre_le_unipotent_radical hJ H hh, fun z hz g hg => Z_comm hJ H hh hz hg, fun y y' => ?_,
    fun g hg z hz => N_norm_Z hJ H hh hg hz, fun g hg y => ?_, fun g hg z hz => H_comm_Z hJ H hh hg hz⟩
  · exact Md.continuous_into_HA hJ (continuous_sLmat P T _ hcy)
  · exact ⟨fun a => ⟨_, isWp_yH hJ H hh g a⟩, fun a => rfl, inv_mul_mem_Z hJ H hh hg⟩
  · exact (yH_mul_Z hJ H hh (sHG_mem hJ H hh _) hz a).trans (yH_sHG hJ H hh _ a)
  · exact heisenberg_cocycle_mem_centre hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E))
      (y' := fun a => (y' a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2) (fun a => (y' a).2)
      (fun a => ((y + y') a).2)
  · exact ⟨fun a => ⟨lin (Af F) σ J g (y a), H_isWp hJ H hh hg (y a).2⟩, fun a => rfl,
      H_conj_sHG hJ H hh hg _ _⟩

theorem heisenberg_parabolic_all : PI.LevelKSplit.W.NC.HeisPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact heisenberg_parabolic F E σ M J

end PI.LevelKSplit.W.NCH
