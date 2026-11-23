import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isClosedEmbedding_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) : IsClosedEmbedding (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  set P' := (frameMat B A d.ι).map (incA D)
  set Q' := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D)
  have hv : Continuous fun g : GA D B => mt B g := Units.continuous_val.comp continuous_subtype_val
  have hvi : Continuous fun g : GA D B => mt B g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  let Φ : GA D B → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E) ×
      (Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E))ᵐᵒᵖ :=
    fun g => (Q' * mt B g * P', MulOpposite.op (Q' * mt B g⁻¹ * P'))
  have hΦ : Continuous Φ :=
    ((continuous_const.matrix_mul hv).matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul hvi).matrix_mul continuous_const))
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)
  have hcomp : Φ ∘ stabilizerEmbedding d = (Units.embedProduct _) ∘ (fun h : GA D A => matHom A h) := by
    funext h
    have e : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ := map_inv φ h
    simp only [Function.comp_apply, Φ, Units.embedProduct_apply]
    refine Prod.ext ?_ ?_
    · exact (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h).symm
    · show MulOpposite.op (Q' * mt B (stabilizerEmbedding d h)⁻¹ * P') = _
      rw [← e]
      exact congrArg MulOpposite.op (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h⁻¹).symm
  have hind : IsInducing (stabilizerEmbedding d) := by
    refine IsInducing.of_comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d) hΦ ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp (IsInducing.subtypeVal (t := ((HR (AF D.host.F) D.sp.cm.sig A.gram : Subgroup _) : Set (GL (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)))))
  have hrange : Set.range (stabilizerEmbedding d) = {g : GA D B | mt B g * d.a.map (incA D) = d.a.map (incA D)} := by
    ext g
    constructor
    · rintro ⟨h, rfl⟩
      exact GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d h
    · intro hg
      exact GlobalTheory.UnitaryEmbeddingGroup.mem_range_of_fix d hε g hg
  have hcl : IsClosed (Set.range (stabilizerEmbedding d)) := by
    rw [hrange]
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    exact isClosed_eq (hv.matrix_mul continuous_const) continuous_const
  exact ⟨⟨hind, GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_injective d⟩, hcl⟩

end GlobalTheory.UnitaryEmbeddingVolume

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

theorem vol_pos_lt_top : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)),
    IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ μ : Measure (GfC Y), μ.IsHaarMeasure →
      MeasurableSet {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      0 < μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} < ⊤ := by
  intro D Y V d Λ 𝔪 hΛ h𝔪 μ hμ
  obtain ⟨hU, hK⟩ := congLev_open_compact V hΛ.1 h𝔪
  set S := {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪}
  have hc : Continuous fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d).comp continuous_subtype_val
  have hS : S = (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      (((congLev D.sp.cm V.gram Λ 𝔪).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  have hopen : IsOpen S := by
    rw [hS]; exact hU.preimage hc
  have h1 : (1 : GfC Y) ∈ S := by
    show Lev.finE V (stabilizerEmbedding d ((1 : GfC Y) : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪
    rw [OneMemClass.coe_one, show stabilizerEmbedding d (1 : GA D Y) = 1 from
      map_one (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)), map_one]
    exact (congLev D.sp.cm V.gram Λ 𝔪).one_mem
  have hce : IsClosedEmbedding fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (isClosedEmbedding_unitaryEmbedding d one_ne_zero).comp (GlobalTheory.Ker.CongTop.isClosed_GfC Y).isClosedEmbedding_subtypeVal
  have hsub : S ⊆ (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      ((Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Subgroup (GA D V)) : Set (GA D V)) := by
    intro b hb
    refine ⟨?_, hb⟩
    show stabilizerEmbedding d (b : GA D Y) ∈ GfC V
    rw [GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff, ← GlobalTheory.UnitaryEmbeddingGroup.map_eq_one_iff d, ← GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff]
    exact b.2
  refine ⟨hopen.measurableSet, hopen.measure_pos μ ⟨1, h1⟩, ?_⟩
  exact (measure_mono hsub).trans_lt (hce.isCompact_preimage hK).measure_lt_top

end GlobalTheory.UnitaryEmbeddingVolume
