import Mathlib
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm

noncomputable section

open NumberField MeasureTheory GroundTheory.Global nonZeroDivisors in
theorem PositivityTheory.ThKCT.Tate.transport {K G : Type} [Field K] [NumberField K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (e : G ≃ₜ* IdeleGroup K) (μ : Measure G) [μ.IsHaarMeasure] {z : ℝ} (hz : 1 < z) {k : ℕ}
    (hk : 2 * z + 2 < k) (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∫⁻ l, ENNReal.ofReal (infiniteZetaBound z k (IdeleGroup.toInfinite K (e l)) *
      finiteZetaBound L z (IdeleGroup.toFinite K (e l))) ∂μ < ⊤ := by
  have h2 := (integrable_zetaBound (K := K) hz hk L).smul_measure_nnreal (c := (μ.map e).haarScalarFactor (ideleMeasure K))
  rw [← Measure.isMulLeftInvariant_eq_smul] at h2
  exact (h2.comp_measurable e.continuous.measurable).lintegral_lt_top

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

namespace Tate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F E) in

abbrev Φ : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem cont_Φ : Continuous (Φ F E) := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).toLinearMap

theorem cont_Φ_symm : Continuous (Φ F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := (ideleTop F E).1.1
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).symm.toLinearMap

variable (F E) in

def Ψ : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (Φ F E).toMulEquiv
  continuous_toFun := Continuous.units_map (Φ F E).toMulEquiv.toMonoidHom cont_Φ
  continuous_invFun := Continuous.units_map (Φ F E).symm.toMulEquiv.toMonoidHom cont_Φ_symm

theorem Ψ_val (l : (AE F E)ˣ) : ((Ψ F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = Φ F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) : (absE F E l : ℝ) = IdeleGroup.ideleModule E (Ψ F E l) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), IdeleGroup.ideleModule_apply, IdeleGroup.infiniteModule,
    IdeleGroup.finiteModule, coe_ideleNorm, Ψ_val, Algebra.norm_eq_of_algEquiv, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul,
    NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow]
    rfl
  · rw [show ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) = _ from
      NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)]
    refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

theorem ext_map (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding)
    (b : InfiniteAdeleRing F) :
    InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) b W) =
      InfinitePlace.Completion.extensionEmbedding w (b w) := by
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    ((InfinitePlace.Completion.isometry_extensionEmbedding W).continuous.comp ((continuous_apply W).comp
      (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap (K := F) (L := E))))
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)) (funext fun k => ?_)) b
  change InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E)
    (algebraMap F (InfiniteAdeleRing F) k) W) = _
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
  exact (InfinitePlace.Completion.extensionEmbedding_coe W ((WithAbs.equiv W.1).symm (algebraMap F E k))).trans
    ((RingHom.congr_fun h k).trans (InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm k)).symm)

theorem ext_Φ (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding) (l : AE F E) :
    InfinitePlace.Completion.extensionEmbedding W ((Φ F E l).1 W) = piInf (⟨W.embedding, h⟩ : EmbOver E w) l := by
  induction l using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]; exact map_add _ _ _
  | tmul a x =>
    rw [adeleTensorAlgEquivLeft_tmul]
    change InfinitePlace.Completion.extensionEmbedding W ((algebraMap E (AdeleRing (𝓞 E) E) x).1 W *
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) a.1 W) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * W.embedding x
    rw [map_mul, ext_map W h, mul_comm]
    exact congrArg _ (InfinitePlace.Completion.extensionEmbedding_coe W ((WithAbs.equiv W.1).symm x))

theorem norm_le (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : InfinitePlace E) (l : (AE F E)ˣ) :
    ‖(Φ F E l).1 W‖ ≤ ∑ w, ‖piInf (τ w) (l : AE F E)‖ := by
  haveI := h.1
  let w := InfinitePlace.mk (W.embedding.comp (algebraMap F E))
  have hw : W.embedding.comp (algebraMap F E) = w.embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal w))).symm
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding W).norm_map_of_map_zero (map_zero _), ext_Φ W hw]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun w => ‖piInf (τ w) (l : AE F E)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ w))
  have := (GlobalTheory.Doubling.absEw_eq_sq h (⟨W.embedding, hw⟩ : EmbOver E w) (GlobalTheory.Doubling.unitInf F E w l)).symm.trans
    (GlobalTheory.Doubling.absEw_eq_sq h (τ w) (GlobalTheory.Doubling.unitInf F E w l))
  exact congrArg NNReal.toReal ((pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 this)

theorem snd_eq {l c : AE F E} (h : At (evI F) (l - c)) : (Φ F E l).2 = (Φ F E c).2 := by
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have h0 := congrArg (Φ F E) (h u (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)))
  rw [map_smul, map_zero, map_sub, Algebra.smul_def] at h0
  have h1 := congrArg Prod.snd h0
  change finiteAdeleMap F E 1 * ((Φ F E l).2 - (Φ F E c).2) = 0 at h1
  rwa [map_one, one_mul, sub_eq_zero] at h1

end Tate

theorem tateAbs : TateAbs := by
  intro F E _ _ _ _ _ σ B hB μ hμ z hz
  classical
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  have hz1 : (1 : ℝ) < z := by exact_mod_cast hz
  have hk : 2 * (z : ℝ) + 2 < (2 * z + 3 : ℕ) := by push_cast; linarith
  refine ⟨(2 * z + 3) * Fintype.card (InfinitePlace E), fun C hC => ?_⟩
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hC.image (continuous_snd.comp (Tate.cont_Φ (F := F) (E := E))))
  refine lt_of_le_of_lt ?_ (Tate.transport (Tate.Ψ F E) μ hz1 hk L)
  have hT : IsOpen {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L} :=
    (isOpen_idealFiniteAdeles L).preimage (continuous_snd.comp (Tate.cont_Φ.comp Units.continuous_val))
  refine le_trans (lintegral_mono_set (t := {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L})
    fun l ⟨c, hc, hl⟩ => hL ⟨c, hc, (Tate.snd_eq hl).symm⟩) ?_
  refine le_trans (setLIntegral_mono' hT.measurableSet fun l hl => ENNReal.ofReal_le_ofReal ?_) (setLIntegral_le_lintegral _ _)
  have hm : (IdeleGroup.toFinite E (Tate.Ψ F E l) : FiniteAdeleRing (𝓞 E) E) ∈ idealFiniteAdeles L := hl
  rw [finiteZetaBound, if_pos hm, Tate.absE_eq, ← Real.rpow_natCast, ideleModule_rpow_eq, infiniteZetaBound,
    Finset.prod_div_distrib, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_left (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (IdeleGroup.finiteModule_pos _).le _)) (Finset.prod_pos fun _ _ => by positivity) ?_
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun W _ => pow_le_pow_left₀ (by positivity) ?_ _
  exact add_le_add le_rfl (Tate.norm_le hB.cm B.emb W l)

end PositivityTheory.ThKCT

end
