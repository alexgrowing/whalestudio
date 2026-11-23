import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchHeis GlobalTheory.ThK
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchKX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def archActX (M : Model σ X W) (g : UA σ X.J)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  coordI M (actAB (cA σ) (g, (1 : UA σ W.J)) (M.co.e.symm (liftV v.1, liftV v.2)))

theorem locOpInf_schrF (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J) (hg : g ∈ UAt σ X (evI F))
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) ⇑f ⇑f₁)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
    (f f₁ : SInf F (Fin n × Fin d)) (hf₁ : ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f) :
    ⇑(locOpInf (om (g, 1)) f₁) = schrF (trP F (Fin n × Fin d)) (archActX M g v) ⇑(locOpInf (om (g, 1)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  set u' := actAB (cA σ) (g, (1 : UA σ W.J)) u with hu'
  have h0 : ∀ c : AF F, evI F c = 0 → c • u = 0 := by
    intro c hc
    have hl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, c • liftV y = 0 := by
      intro y
      funext i
      refine Prod.ext ?_ ?_
      · change c.1 * _ = 0
        rw [fst_eq_zero_of_ev hc, zero_mul]
      · change c.2 * 0 = 0
        rw [mul_zero]
    rw [hu, ← LinearEquiv.map_smul, Prod.smul_mk, hl, hl, Prod.mk_zero_zero, LinearEquiv.map_zero]
  have hAt : ∀ c : AF F, evI F c = 0 → c • u' = 0 := by
    intro c hc
    have hm : c • (mat g - 1) = 0 := hg c hc
    have e : u' = (mat g - 1) * u + u := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel, hu']
      simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
      rfl
    rw [e, smul_add, ← Matrix.smul_mul, hm, Matrix.zero_mul, zero_add, h0 c hc]
  have hAt₁ : At (evI F) (M.co.e u').1 := by
    intro c hc
    have := congrArg Prod.fst (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have hAt₂ : At (evI F) (M.co.e u').2 := by
    intro c hc
    have := congrArg Prod.snd (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have he' : M.co.e u' = (liftV (archActX M g v).1, liftV (archActX M g v).2) := by
    change M.co.e u' = (liftV (locV (M.co.e u').1), liftV (locV (M.co.e u').2))
    rw [liftV_locV_of_at hAt₁, liftV_locV_of_at hAt₂]
  have hA₁ := acts_locOpInf (hex f₁) (refFin _) (rest_refFin _ f₁)
  have hA := acts_locOpInf (hex f) (refFin _) (rest_refFin _ f)
  have himpl := hS.impl (g, 1) u (tens (evI F) ⇑f (refFin _)) (rest_refFin _ f).2
  have h1 : M.co.rho ψ u (tens (evI F) ⇑f (refFin _)) = tens (evI F) ⇑f₁ (refFin _) := by
    simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
    rw [schr_tens ψ hψ v, hf₁]
  have h2 : M.co.rho ψ u' (tens (evI F) ⇑(locOpInf (om (g, 1)) f) (refFin _)) =
      tens (evI F) (schrF (trP F (Fin n × Fin d)) (archActX M g v) ⇑(locOpInf (om (g, 1)) f)) (refFin _) := by
    simp only [Darboux.rho]
    rw [he', schr_tens ψ hψ]
  rw [h1, hA₁, hA, ← hu', h2] at himpl
  funext y
  have := congrFun himpl (liftV y)
  simp only [tens, refFin_liftV, mul_one] at this
  have hy : (fun i => evI F (liftV y i)) = y := funext fun i => evI_liftV y i
  rwa [hy] at this

end GlobalTheory.ArchKX

namespace GlobalTheory.ArchKX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_one (g : UA σ X.J) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) (g, (1 : UA σ W.J)) u = mat g * u := by
  simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  rfl

theorem isLinearMap_archActX (M : Model σ X W) (g : UA σ X.J) : IsLinearMap ℝ (archActX M g) where
  map_add v w := by
    simp only [archActX, actAB_one, Prod.fst_add, Prod.snd_add, lift_add, ← Prod.mk_add_mk, map_add,
      Matrix.mul_add, coordI_add]
  map_smul c v := by
    simp only [archActX, actAB_one, Prod.smul_fst, Prod.smul_snd, lift_smul, ← Prod.smul_mk, map_smul,
      Matrix.mul_smul, coordI_smul]

theorem archActX_inv (M : Model σ X W) (g : UA σ X.J) (v) : archActX M g (archActX M g⁻¹ v) = v := by
  have e : archActX M g⁻¹ v = coordI M (mat g⁻¹ * M.co.e.symm (liftV v.1, liftV v.2)) := by
    rw [archActX, actAB_one]
  rw [archActX, e, lift_coordI, actAB_one, Matrix.mul_smul, coordI_one, ← Matrix.mul_assoc,
    GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul, coordI_lift]

end GlobalTheory.ArchKX

namespace GlobalTheory.ArchKX

open MeasureTheory GlobalTheory.ArchIsom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem lintegral_acts_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (hμ : μ.IsAddHaarMeasure)
    (g : UA σ X.J) (f f₁ : SInf F (Fin n × Fin d)) (hact : Acts (evI F) (om (g, 1)) ⇑f ⇑f₁) :
    ∫⁻ x, ‖f₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hU := (IsUWeilPair.isUSplitting hW).unit
  haveI := hμ
  have hΦ := hact (r0 F (Fin n × Fin d)) (restriction_at_standard_point _ f)
  letI mB : MeasurableSpace (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
  let ν : Measure (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
  let H : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)) ≃ₜ
      (Fin n × Fin d → AF F) :=
    { (splitEquiv F (Fin n × Fin d)).toEquiv with
      continuous_toFun := continuous_splitEquiv _
      continuous_invFun := continuous_splitEquiv_symm _ }
  let e := H.toMeasurableEquiv
  have he : ∀ p, e p = splitEquiv F (Fin n × Fin d) p := fun _ => rfl
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite μ := inferInstance
  have hμ' : (Measure.map e (μ.prod ν)).IsAddHaarMeasure :=
    (splitEquiv F (Fin n × Fin d)).isAddHaarMeasure_map (μ.prod ν) (continuous_splitEquiv _)
      (continuous_splitEquiv_symm _)
  have hmem : tens (evI F) (⇑f) (r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) := (restriction_at_standard_point _ f).2
  have hu := hU (Measure.map e (μ.prod ν)) hμ' (g, 1) _ hmem
  rw [hΦ, lintegral_tensor_at_standard_point _ μ ν e he, lintegral_tensor_at_standard_point _ μ ν e he] at hu
  have hc0 : ν (intPts F (Fin n × Fin d)) ≠ 0 :=
    ((isOpen_intPts _).measure_pos ν ⟨0, zero_mem_intPts _⟩).ne'
  have hct : ν (intPts F (Fin n × Fin d)) ≠ ⊤ := (isCompact_intPts _).measure_lt_top.ne
  exact (ENNReal.mul_left_inj hc0 hct).mp hu

theorem lintegral_acts_eq_volume (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J) (f f₁ : SInf F (Fin n × Fin d))
    (hact : Acts (evI F) (om (g, 1)) ⇑f ⇑f₁) : ∫⁻ x, ‖f₁ x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := MeasurableAdd₂.toMeasurableAdd
  haveI : (volume : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact lintegral_acts_eq M ψ χX χW om hW volume inferInstance g f f₁ hact

end GlobalTheory.ArchKX

namespace GlobalTheory.ArchKX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

omit [NumberField E] in
theorem continuous_locV (κ : Type) : Continuous (locV (F := F) (κ := κ)) :=
  continuous_pi fun i => GlobalTheory.ArchIsom.continuous_toMixed.comp (continuous_fst.comp (continuous_apply i))

theorem continuous_archActX (M : Model σ X W) (v) : Continuous fun g : UA σ X.J => archActX M g v := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : UA σ X.J => mat g * M.co.e.symm (liftV v.1, liftV v.2) :=
    hm.matrix_mul continuous_const
  haveI hP : IsModuleTopology (AF F) (Fin n → Fin d → AE F E) := inferInstance
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) := hP
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  simp only [archActX, actAB_one, coordI]
  exact ((continuous_locV _).comp (continuous_fst.comp (he.comp h1))).prodMk
    ((continuous_locV _).comp (continuous_snd.comp (he.comp h1)))

theorem archActX_bound (M : Model σ X W) (S : Set (UA σ X.J)) (hS : IsCompact S) :
    ∃ C : ℝ, ∀ g ∈ S, ∀ v, ‖archActX M g v‖ ≤ C * ‖v‖ := by
  classical
  let b := Module.finBasis ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
  have hB : ∀ j, ∃ B : ℝ, ∀ g ∈ S, ‖archActX M g (b j)‖ ≤ B := fun j =>
    hS.exists_bound_of_continuousOn (continuous_archActX M (b j)).continuousOn
  choose B hB using hB
  let c := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  refine ⟨∑ j, ‖c j‖ * B j, fun g hg v => ?_⟩
  let T := IsLinearMap.mk' _ (isLinearMap_archActX M g)
  have hv : archActX M g v = ∑ j, b.coord j v • archActX M g (b j) := by
    change T v = ∑ j, b.coord j v • T (b j)
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [hv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  have h1 : ‖b.coord j v‖ ≤ ‖c j‖ * ‖v‖ := (c j).le_opNorm v
  have h2 := hB j g hg
  have h3 : 0 ≤ B j := (norm_nonneg _).trans h2
  calc ‖b.coord j v‖ * ‖archActX M g (b j)‖ ≤ (‖c j‖ * ‖v‖) * B j :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖c j‖ * B j * ‖v‖ := by ring

end GlobalTheory.ArchKX
