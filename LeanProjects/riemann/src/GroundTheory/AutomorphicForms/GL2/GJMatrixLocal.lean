import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs

namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.LocalField GroundTheory.Automorphic.GodementJacquet MeasureTheory Measure Filter Topology Matrix

noncomputable section

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Space

variable (F) {ι : Type*} [Fintype ι]

def localSchwartzBruhatPi : Submodule ℂ ((ι → F) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.comp_left (smul_zero c)⟩

omit [Field F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [Fintype ι] in
theorem mem_localSchwartzBruhatPi {f : (ι → F) → ℂ} :
    f ∈ localSchwartzBruhatPi F ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

variable {F}

def localTensor (g : ι → F → ℂ) : (ι → F) → ℂ :=
  fun x ↦ ∏ i, g i (x i)

theorem localTensor_mem {g : ι → F → ℂ} (hg : ∀ i, g i ∈ schwartzBruhat F) :
    localTensor g ∈ localSchwartzBruhatPi F := by
  refine ⟨?_, ?_⟩
  · have : localTensor g = ∏ i, fun x : ι → F ↦ g i (x i) := by
      funext x
      simp only [localTensor, Finset.prod_apply]
    rw [this]
    exact Finset.prod_induction _ IsLocallyConstant (fun _ _ ha hb ↦ ha.mul hb)
      (IsLocallyConstant.const 1) fun i _ ↦ (hg i).1.comp_continuous (continuous_apply i)
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i ↦ (hg i).2.isCompact) fun x hx ↦ ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

theorem cosetInd_valBall_mem (N : ℤ) (a : F) : cosetInd (valBall F N) a ∈ schwartzBruhat F := by
  classical
  refine ⟨isLocallyConstant_of_add_valBall (N := N) fun x h hh ↦ ?_, ?_⟩
  · rw [cosetInd_apply, cosetInd_apply, add_sub_right_comm x h a,
      AddSubgroup.add_mem_cancel_right _ hh]
  · refine HasCompactSupport.intro ((isCompact_valBall N).image (continuous_const_add a))
      fun x hx ↦ ?_
    rw [cosetInd_apply, if_neg]
    intro hxa
    exact hx ⟨x - a, hxa, add_sub_cancel a x⟩

theorem localSchwartzBruhatPi_eq_span :
    localSchwartzBruhatPi F (ι := ι) = Submodule.span ℂ (Set.range fun p : ℤ × (ι → F) ↦
      localTensor fun i ↦ cosetInd (valBall F p.1) (p.2 i)) := by
  refine le_antisymm (fun f hf ↦ ?_) (Submodule.span_le.mpr ?_)
  · have hopen : ∀ H ∈ Set.range (valBall F), IsOpen (H : Set F) := by
      rintro _ ⟨N, rfl⟩
      exact isOpen_valBall N
    have hbasis : ∀ W ∈ 𝓝 (0 : F), ∃ H ∈ Set.range (valBall F), (H : Set F) ⊆ W := by
      intro W hW
      obtain ⟨N, -, hN⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hW
      exact ⟨_, ⟨N, rfl⟩, hN⟩
    obtain ⟨_, ⟨N, rfl⟩, s, hs⟩ := exists_eq_sum_prod_cosetInd hopen hbasis hf.1 hf.2
    rw [hs]
    exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨(N, a), rfl⟩)
  · rintro _ ⟨p, rfl⟩
    exact localTensor_mem fun i ↦ cosetInd_valBall_mem p.1 (p.2 i)

end Space

section Fourier

variable [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι] (ψ : AddChar F Circle)

def localMeasurePi : Measure (ι → F) :=
  Measure.pi fun _ ↦ selfDualMeasure ψ

instance : (localMeasurePi ψ (ι := ι)).IsAddHaarMeasure := by
  unfold localMeasurePi
  infer_instance

def localFourierPi (f : (ι → F) → ℂ) (y : ι → F) : ℂ :=
  ∫ x, f x * (ψ (∑ i, x i * y i) : ℂ) ∂localMeasurePi ψ

variable {ψ}

theorem integrable_of_mem_localSchwartzBruhatPi {f : (ι → F) → ℂ}
    (hf : f ∈ localSchwartzBruhatPi F) : Integrable f (localMeasurePi ψ) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem localFourierPi_smul (c : ℂ) (f : (ι → F) → ℂ) :
    localFourierPi ψ (c • f) = c • localFourierPi ψ f := by
  funext y
  simp only [localFourierPi, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem localFourierPi_zero : localFourierPi ψ (0 : (ι → F) → ℂ) = 0 := by
  funext y
  simp [localFourierPi]

theorem localFourierPi_localTensor (g : ι → F → ℂ) :
    localFourierPi ψ (localTensor g) =
      localTensor fun i ↦ localFourier (selfDualMeasure ψ) ψ (g i) := by
  funext y
  have h := integral_fintype_prod_eq_prod (μ := fun _ : ι ↦ selfDualMeasure ψ)
    (fun i x ↦ g i x * (ψ (x * y i) : ℂ))
  rw [localFourierPi, localTensor]
  simp only [localFourier]
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [localTensor]
  rw [addChar_sum ψ Finset.univ fun i ↦ x i * y i, ← Finset.prod_mul_distrib]

variable (hψ : Continuous ψ)
include hψ

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_char_sum_mul (y : ι → F) :
    Continuous fun x : ι → F ↦ (ψ (∑ i, x i * y i) : ℂ) :=
  continuous_subtype_val.comp (hψ.comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const))

theorem integrable_mul_char_sum {f : (ι → F) → ℂ} (hf : Integrable f (localMeasurePi ψ))
    (y : ι → F) :
    Integrable (fun x ↦ f x * (ψ (∑ i, x i * y i) : ℂ)) (localMeasurePi ψ) :=
  hf.mono (hf.1.mul (continuous_char_sum_mul hψ y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem localFourierPi_add {f g : (ι → F) → ℂ} (hf : Integrable f (localMeasurePi ψ))
    (hg : Integrable g (localMeasurePi ψ)) :
    localFourierPi ψ (f + g) = localFourierPi ψ f + localFourierPi ψ g := by
  funext y
  simp only [localFourierPi, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_char_sum hψ hf y) (integrable_mul_char_sum hψ hg y)

variable (hψ1 : ψ ≠ 1)
include hψ1

theorem localFourierPi_mem {f : (ι → F) → ℂ} (hf : f ∈ localSchwartzBruhatPi F) :
    localFourierPi ψ f ∈ localSchwartzBruhatPi F := by
  rw [localSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hg
    rw [localFourierPi_localTensor]
    exact localTensor_mem fun i ↦
      localFourier_mem_schwartzBruhat _ hψ hψ1 (cosetInd_valBall_mem N (a i))
  | zero => rw [localFourierPi_zero]; exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← localSchwartzBruhatPi_eq_span] at hg hh
    rw [localFourierPi_add hψ (integrable_of_mem_localSchwartzBruhatPi hg)
      (integrable_of_mem_localSchwartzBruhatPi hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    rw [localFourierPi_smul]
    exact Submodule.smul_mem _ c ih

theorem localFourierPi_localFourierPi {f : (ι → F) → ℂ} (hf : f ∈ localSchwartzBruhatPi F) :
    localFourierPi ψ (localFourierPi ψ f) = fun x ↦ f (-x) := by
  rw [localSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hg
    rw [localFourierPi_localTensor, localFourierPi_localTensor]
    funext x
    simp only [localTensor, Pi.neg_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [localFourier_localFourier_selfDual hψ hψ1 (cosetInd_valBall_mem N (a i))]
  | zero => funext x; simp [localFourierPi_zero]
  | add g h hg hh ihg ihh =>
    rw [← localSchwartzBruhatPi_eq_span] at hg hh
    rw [localFourierPi_add hψ (integrable_of_mem_localSchwartzBruhatPi hg)
        (integrable_of_mem_localSchwartzBruhatPi hh),
      localFourierPi_add hψ
        (integrable_of_mem_localSchwartzBruhatPi (localFourierPi_mem hψ hψ1 hg))
        (integrable_of_mem_localSchwartzBruhatPi (localFourierPi_mem hψ hψ1 hh)), ihg, ihh]
    rfl
  | smul c g _ ih =>
    rw [localFourierPi_smul, localFourierPi_smul, ih]
    rfl

end Fourier

section Matrix

variable {n : ℕ}

omit [Field F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem isSchwartzBruhat_iff_comp_symm (Φ : Matrix (Fin n) (Fin n) F → ℂ) :
    IsSchwartzBruhat Φ ↔
      Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm ∈ localSchwartzBruhatPi F := by
  set e := matrixCoordHomeomorph (Fin n) F
  have hΦ : Φ = (Φ ∘ e.symm) ∘ e := by
    funext x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  constructor
  · rintro ⟨hlc, hcs⟩
    exact ⟨hlc.comp_continuous e.symm.continuous, hcs.comp_homeomorph e.symm⟩
  · rintro ⟨hlc, hcs⟩
    rw [hΦ]
    exact ⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)

def localMatrixFourier (Φ : Matrix (Fin n) (Fin n) F → ℂ) (y : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∫ x, Φ x * (ψ (trace (x * y)) : ℂ) ∂matrixMeasure (selfDualMeasure ψ)

theorem localMatrixFourier_eq (Φ : Matrix (Fin n) (Fin n) F → ℂ) (y : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ Φ y =
      localFourierPi ψ (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) (matrixCoordT y) := by
  set e := matrixCoordHomeomorph (Fin n) F
  rw [localFourierPi, localMeasurePi, ← (measurePreserving_matrixCoord (n := Fin n)
    (selfDualMeasure ψ)).integral_comp e.measurableEmbedding, localMatrixFourier]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Function.comp_apply, trace_mul_eq_sum]
  rfl

theorem _root_.GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.localMatrixFourier
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) : IsSchwartzBruhat (GJMatrix.localMatrixFourier ψ Φ) := by
  have hG := localFourierPi_mem hψ hψ1 ((isSchwartzBruhat_iff_comp_symm Φ).mp hΦ)
  have he : GJMatrix.localMatrixFourier ψ Φ =
      localFourierPi ψ (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) ∘
        matrixCoordTHomeomorph (Fin n) F := by
    funext y
    rw [localMatrixFourier_eq]
    rfl
  rw [he]
  exact ⟨hG.1.comp_continuous (matrixCoordTHomeomorph (Fin n) F).continuous,
    hG.2.comp_homeomorph (matrixCoordTHomeomorph (Fin n) F)⟩

theorem localMatrixFourier_localMatrixFourier {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (x : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (localMatrixFourier ψ Φ) x = Φ (-x) := by
  set e := matrixCoordHomeomorph (Fin n) F
  set eT := matrixCoordTHomeomorph (Fin n) F
  set G := Φ ∘ e.symm
  have hG : G ∈ localSchwartzBruhatPi F := (isSchwartzBruhat_iff_comp_symm Φ).mp hΦ
  have h1 : localMatrixFourier ψ (localMatrixFourier ψ Φ) x =
      ∫ y, localFourierPi ψ G (matrixCoordT y) *
        (ψ (∑ p, matrixCoordT y p * matrixCoord x p) : ℂ) ∂matrixMeasure (selfDualMeasure ψ) := by
    rw [localMatrixFourier]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [localMatrixFourier_eq, trace_mul_comm, trace_mul_eq_sum]
    simp only [mul_comm (matrixCoord x _)]
    rfl
  have h2 := (measurePreserving_matrixCoordT (n := Fin n) (selfDualMeasure ψ)).integral_comp
    eT.measurableEmbedding
    (fun z ↦ localFourierPi ψ G z * (ψ (∑ p, z p * matrixCoord x p) : ℂ))
  rw [h1, h2]
  have h3 := congrFun (localFourierPi_localFourierPi hψ hψ1 hG) (matrixCoord x)
  rw [localFourierPi] at h3
  rw [← localMeasurePi, h3]
  simp only [G, Function.comp_apply]
  congr 1

end Matrix

end

end GroundTheory.Automorphic.GJMatrix
