import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

def intFin : Set (Af F) := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_intFin : IsOpen (intFin F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)

theorem isCompact_intFin : IsCompact (intFin F) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem sub_archIn_apply (w : κ → AF F) (i : κ) :
    (w - archIn F κ (archOut F κ w)) i = ((0 : Ainf F), (w i).2) := by
  have h : archIn F κ (archOut F κ w) i = infAd F (evI F (w i)) := by
    rw [archIn_apply, archOut_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [Pi.sub_apply, h]
  refine Prod.ext ?_ ?_
  · change (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1) = 0
    rw [RingEquiv.symm_apply_apply, sub_self]
  · change (w i).2 - 0 = (w i).2
    rw [sub_zero]

theorem mem_slab_iff (m : ℕ) (hm : 0 < m) (w : κ → AF F) :
    w ∈ slab F κ m ↔ ∀ i, algebraMap F (Af F) ((m : F)⁻¹) * (w i).2 ∈ intFin F := by
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hc : algebraMap F (Af F) ((m : F)⁻¹) * (m : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hm0, map_one]
  change (∀ i, ∃ a : AF F, _ ∧ _ ∧ _) ↔ _
  refine forall_congr' fun i => ?_
  rw [sub_archIn_apply]
  constructor
  · rintro ⟨a, -, ha, he⟩
    have h2 : (w i).2 = (m : Af F) * a.2 := by
      have := congrArg Prod.snd he
      rw [this]
      change sndA F ((m : AF F) * a) = _
      rw [map_mul, map_natCast]; rfl
    intro v
    rw [h2, ← mul_assoc, hc, one_mul]
    exact ha v
  · intro h
    refine ⟨pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2), ?_, fun v => h v, ?_⟩
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0
      exact map_zero _
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = fstA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul]
        change (0 : Ainf F) = fstA F (m : AF F) * 0
        rw [mul_zero]
      · change (w i).2 = sndA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul, map_natCast]
        change (w i).2 = (m : Af F) * (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2)
        rw [← mul_assoc, mul_comm (m : Af F), hc, one_mul]

theorem isOpen_slab (m : ℕ) (hm : 0 < m) : IsOpen (slab F κ m) := by
  have : slab F κ m = ⋂ i, (fun w : κ → AF F => algebraMap F (Af F) ((m : F)⁻¹) * (w i).2) ⁻¹' intFin F := by
    ext w; rw [mem_slab_iff F κ m hm]; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_intFin F).preimage
    (continuous_const.mul (continuous_snd.comp (continuous_apply i)))

theorem archIn_mem_slab (t : Fin (dimA F κ) → ℝ) : archIn F κ t ∈ slab F κ 1 := by
  rw [mem_slab_iff F κ 1 one_pos]
  intro i v
  have : (archIn F κ t i).2 = 0 := rfl
  rw [this, mul_zero]
  exact zero_mem _

open scoped Pointwise in
theorem slab_open_cube_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  intro F _ _ κ _
  refine ⟨fun m hm => isOpen_slab F κ m hm, fun μ hμ => ?_⟩
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  refine ⟨?_, fun A hA => ?_⟩
  · let U := archOut F κ ⁻¹' (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1) ∩ slab F κ 1
    have hU : IsOpen U :=
      ((isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage (continuous_archOut F κ)).inter
        (isOpen_slab F κ 1 one_pos)
    have hne : U.Nonempty := by
      refine ⟨archIn F κ (fun _ => 1 / 2), ?_, archIn_mem_slab F κ _⟩
      simp only [Set.mem_preimage, archOut_archIn, Set.mem_pi, Set.mem_univ, true_implies]
      intro _; constructor <;> norm_num
    refine lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono ?_)
    exact Set.inter_subset_inter_left _ (Set.preimage_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self))
  · let K : Set (κ → AF F) := (fun y : κ → Af F => fun i => pairA F 0 (y i)) '' Set.univ.pi fun _ => intFin F
    have hK : IsCompact K := by
      refine (isCompact_univ_pi fun _ => isCompact_intFin F).image (continuous_pi fun i => ?_)
      exact (continuous_const.prodMk (continuous_apply i) : Continuous fun y : κ → Af F => ((0 : Ainf F), y i))
    have hsub : archOut F κ ⁻¹' A ∩ slab F κ 1 ⊆ archIn F κ '' A + K := by
      rintro w ⟨hwA, hw⟩
      refine Set.mem_add.2 ⟨archIn F κ (archOut F κ w), ⟨_, hwA, rfl⟩, w - archIn F κ (archOut F κ w),
        ⟨fun i => (w i).2, fun i _ => ?_, funext fun i => (sub_archIn_apply F κ w i).symm⟩, add_sub_cancel _ _⟩
      have h := (mem_slab_iff F κ 1 one_pos w).1 hw i
      rwa [Nat.cast_one, inv_one, map_one, one_mul] at h
    exact ((measure_mono hsub).trans_lt ((hA.image (continuous_archIn F κ)).add hK).measure_lt_top).ne

end GlobalTheory.ArchDecay
