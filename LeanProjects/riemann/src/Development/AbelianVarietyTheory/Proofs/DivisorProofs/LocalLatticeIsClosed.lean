import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatAtClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (F : Type) [Field F] [NumberField F] (v : Pl F) : AddSubgroup (AF F) where
  carrier := {a | At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨fun u _ => by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_add, ha u hu, hb u hu, add_zero]
    · rw [map_add]; exact add_mem ha' hb'
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_neg, ha u hu, neg_zero]
    · rw [map_neg]; exact neg_mem ha'

theorem continuous_evFin' (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_liftV (v : Pl F) : Continuous (GlobalTheory.LatVac.liftV v) := by
  show Continuous fun x => ((0 : Ainf F), singleFin v x)
  exact continuous_const.prodMk (continuous_singleFin v)

theorem isClosed_intAt (v : Pl F) : IsClosed (intAt F v : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have h1 : IsClosed {a : AF F | At (evFin F v) a} := by
    have : {a : AF F | At (evFin F v) a} = ⋂ u : AF F, ⋂ (_ : evFin F v u = 0), {a | u • a = 0} := by
      ext a; simp [At]
    rw [this]
    exact isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq (continuous_const.mul continuous_id) continuous_const
  have h2 : IsClosed {a : AF F | evFin F v a ∈ v.adicCompletionIntegers F} :=
    (GroundTheory.Global.isClosed_adicCompletionIntegers v).preimage (continuous_evFin' v)
  exact h1.inter h2

theorem isCompact_intAt (v : Pl F) : IsCompact (intAt F v : Set (AF F)) := by
  refine ((PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_liftV v)).of_isClosed_subset
    (isClosed_intAt v) ?_
  rintro a ⟨ha, ha'⟩
  refine ⟨evFin F v a, ha', ?_⟩
  rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
  have := GlobalTheory.ThK.partFin_of_at (M := AF F) (v := v) ha
  exact this

theorem isCompact_latAt {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) :
    IsCompact ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  have hZ : (W.L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hxL : ∀ k, x k ∈ W.L := fun k => by
    have : x k ∈ Submodule.span ℤ (Set.range x) := Submodule.subset_span ⟨k, rfl⟩
    rw [hx] at this; exact this
  let g : (Fin m → AF F) → Fin d → AE F E := fun c => ∑ k, c k • fun i => inclR (F := F) (AF F) (x k i)
  have hg : Continuous g :=
    continuous_finset_sum _ fun k _ => by
      have hk : Continuous fun c : Fin m → AF F => c k := continuous_apply k
      exact hk.smul (continuous_const (y := fun i => inclR (F := F) (AF F) (x k i)))
  have heq : ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) =
      g '' Set.pi Set.univ fun _ => (intAt F v : Set (AF F)) := by
    ext z
    constructor
    · intro hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, ha', y, hy, rfl⟩ := hy
        have hy' : y ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hy
        obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        refine ⟨fun k => n k • a, fun k _ => zsmul_mem (show a ∈ intAt F v from ⟨ha, ha'⟩) _, ?_⟩
        funext i
        simp only [g, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_comm a, smul_assoc]
      | zero => exact ⟨0, fun k _ => zero_mem _, by simp [g]⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        exact ⟨c + c', fun k _ => add_mem (hc k trivial) (hc' k trivial), by
          simp only [g, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      | neg y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨-c, fun k _ => neg_mem (hc k trivial), by
          simp only [g, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
    · rintro ⟨c, hc, rfl⟩
      refine sum_mem fun k _ => AddSubgroup.subset_closure ⟨c k, (hc k trivial).1, (hc k trivial).2, x k, hxL k, rfl⟩
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_intAt v).image hg

theorem isClosed_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ)
    (W : Spc F E d), W.L.IsLattice E → ∀ v : Pl F,
    IsClosed ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  intro F E _ _ _ _ _ d W hL v
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  exact (isCompact_latAt W hL v).isClosed

end GlobalTheory.LatAtClosed
