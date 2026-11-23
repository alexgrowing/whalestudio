import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.HaarFinVol

open GlobalTheory.FlagMeas

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def entP (y : GL (Fin j) (Cinf E)) : InfinitePlace E → Fin j → Fin j → ℂ :=
  fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w

def ent (y : GL (Fin j) (Cinf E)) : MatInf E j := entP E j y

def swapH : Matrix (Fin j) (Fin j) (Cinf E) ≃ₜ (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun M w a b := M a b w
  invFun x := Matrix.of fun a b w => x w a b
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun w => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun w =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply w))

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin j) (Cinf E) → Matrix (Fin j) (Fin j) (Cinf E)) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin j) (α := Cinf E)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin j) (R := ℂ) (α := Cinf E)
  have : CompleteSpace (Matrix (Fin j) (Fin j) (Cinf E)) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

theorem isOpenEmbedding_entP : IsOpenEmbedding (entP E j) :=
  (swapH E j).isOpenEmbedding.comp (isOpenEmbedding_val E j)

theorem ent_mul (x y : GL (Fin j) (Cinf E)) : ent E j (x * y) = ent E j x * ent E j y := by
  funext w a b
  change (((x * y : GL (Fin j) (Cinf E)) : Matrix (Fin j) (Fin j) (Cinf E)) a b w) =
    (Matrix.of (ent E j x w) * Matrix.of (ent E j y w)) a b
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_apply]
  rfl

theorem detNorm_ent_pos (y : GL (Fin j) (Cinf E)) : 0 < detNorm E j (ent E j y) := by
  unfold detNorm
  refine Finset.prod_pos fun w _ => ?_
  have h1 : Matrix.of (ent E j y w) =
      (y : Matrix (Fin j) (Fin j) (Cinf E)).map (Pi.evalRingHom (fun _ => ℂ) w) := by
    ext a b; rfl
  have h2 : (Matrix.of (ent E j y w)).det = (y : Matrix (Fin j) (Fin j) (Cinf E)).det w := by
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hu : IsUnit (y : Matrix (Fin j) (Fin j) (Cinf E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have h3 : (y : Matrix (Fin j) (Fin j) (Cinf E)).det w ≠ 0 :=
    (hu.map (Pi.evalRingHom (fun _ => ℂ) w)).ne_zero
  rw [h2]
  positivity

theorem haarGL_lt_top_of_isCompact (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsCompact S)
    (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S < ⊤ := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; exact (measure_empty (μ := haarGL E j)).trans_lt ENNReal.zero_lt_top
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hd.continuousOn
  have hm := hpos x0 hx0
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S < ⊤
  rw [withDensity_apply _ hS.isClosed.measurableSet]
  refine (setLIntegral_mono' hS.isClosed.measurableSet
    (g := fun _ => ENNReal.ofReal ((detNorm E j x0)⁻¹ ^ j)) fun x hx => ?_).trans_lt ?_
  · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.2 (hpos x hx).le)
      (inv_anti₀ hm (hmin hx)) j)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top

theorem haarGL_ne_zero_of_isOpen (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsOpen S)
    (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S ≠ 0 := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S ≠ 0
  have hf : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    ((hd.measurable.inv).pow_const j).ennreal_ofReal
  rw [Ne, withDensity_apply_eq_zero' hf.aemeasurable]
  have : {x : InfinitePlace E → Fin j → Fin j → ℂ | ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) ≠ 0} ∩ S = S :=
    Set.inter_eq_right.2 fun x hx => (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos x hx)) j)).ne'
  rw [this]
  exact hS.measure_ne_zero volume hne

theorem haarGL_image_mul (a : MatInf E j) (ha : 0 < detNorm E j a) (T : Set (MatInf E j)) :
    haarGL E j ((fun g => a * g) '' T) = haarGL E j T := by
  obtain ⟨hemb, hmp⟩ := GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j a ha
  have := hemb.map_apply (haarGL E j) ((fun g => a * g) '' T)
  rw [hmp.map_eq, Set.preimage_image_eq T hemb.injective] at this
  exact this

variable [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))]

theorem measurableEmbedding_ent : MeasurableEmbedding (ent E j) :=
  (isOpenEmbedding_entP E j).measurableEmbedding

def nuGL : Measure (GL (Fin j) (Cinf E)) := (haarGL E j).comap (ent E j)

theorem nuGL_apply (s : Set (GL (Fin j) (Cinf E))) : nuGL E j s = haarGL E j (ent E j '' s) :=
  (measurableEmbedding_ent E j).comap_apply _ s

theorem isHaarMeasure_nuGL : (nuGL E j).IsHaarMeasure := by
  have he := isOpenEmbedding_entP E j
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [nuGL_apply]
    refine haarGL_lt_top_of_isCompact E j (entP E j '' K) (hK.image he.continuous) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y
  · intro g
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, nuGL_apply, nuGL_apply]
    have e1 : (fun h => g * h) ⁻¹' s = (fun h => g⁻¹ * h) '' s := by
      ext y; simp [Set.mem_image, eq_inv_mul_iff_mul_eq]
    have e2 : ent E j '' ((fun h => g⁻¹ * h) '' s) =
        (fun x : MatInf E j => ent E j g⁻¹ * x) '' (ent E j '' s) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => ent_mul E j g⁻¹ y
    rw [e1, e2, haarGL_image_mul E j _ (detNorm_ent_pos E j g⁻¹)]
  · intro U hU hne
    rw [nuGL_apply]
    refine haarGL_ne_zero_of_isOpen E j (entP E j '' U) (he.isOpenMap U hU) (hne.image _) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y

end GlobalTheory.HaarFinVol

theorem GlobalTheory.haarGL_finite_pullback : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  intro E _ _ j _ _ ν _ D _ hD
  haveI := GlobalTheory.HaarFinVol.isHaarMeasure_nuGL E j
  have he := GlobalTheory.HaarFinVol.isOpenEmbedding_entP E j
  haveI : LocallyCompactSpace (GL (Fin j) (Cinf E)) := he.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin j) (Cinf E)) := he.isEmbedding.secondCountableTopology
  have h2 : GlobalTheory.HaarFinVol.nuGL E j {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w :
      GlobalTheory.FlagMeas.MatInf E j) ∈ D} ≤ GlobalTheory.FlagMeas.haarGL E j D :=
    (GlobalTheory.HaarFinVol.nuGL_apply E j _).trans_le (measure_mono fun _ ⟨_, hy, e⟩ => e ▸ hy)
  rw [Measure.isMulLeftInvariant_eq_smul ν (GlobalTheory.HaarFinVol.nuGL E j), Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h2.trans_lt hD)
