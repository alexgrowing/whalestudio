import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.L2BoundedOnSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmoothA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SchurB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopTA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem haarSK_of {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, h1, h2⟩
  · haveI : IsFiniteMeasureOnCompacts μ := ⟨h4⟩
    infer_instance
  · assumption

def mkSD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (hrep : Formalism.MainNotions.S.IsURepOn (GV k r) σ) (hirr : Formalism.MainNotions.S.IsIrredOn (GV k r) σ)
    (w : H) (hw : ‖w‖ = 1) (a C : ℝ) (hdec : ∀ x ∈ GV k r, ‖⟪w, σ x w⟫_ℂ‖ ≤ C * gN x ^ (-a)) : SigData k r :=
  { Hs := H, σ := σ, rep := hrep, irr := hirr, w := w, w_norm := hw, a := a, Cw := C, dec := hdec }

theorem conj_GV_of_UJ {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.MainNotions.S.UJset ε) : P⁻¹ * g * P ∈ GV k r := by
  unfold GV
  obtain ⟨hu, hH⟩ := hP
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hu)
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [← hH]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P := by
        rw [h1, h2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [hg']

theorem irr_of_DSHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}
    (h : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) : Formalism.MainNotions.S.IsIrredOn (GV k r) σ := by
  obtain ⟨P, ⟨hC, -⟩, hDS⟩ := h
  obtain ⟨-, -, -, hirr, -⟩ := hDS
  intro S hS hinv
  exact hirr S hS (fun g hg v hv => hinv _ (conj_GV_of_UJ hC hg) v hv)

theorem sqInt_of_DSHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (h : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) :
    Formalism.MainNotions.S.IsURepOn (GV k r) σ ∧ ∀ v w : H, MemLp (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ) 2 μ := by
  obtain ⟨hU, d, -, hF⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.schurB k r ε lam H σ μ h (haarSK_of hμ)
  refine ⟨hU, fun v w => ?_⟩
  have hc : ContinuousOn (fun g : Mat k r => ⟪w, σ g v⟫_ℂ) (GV k r) :=
    (continuous_inner.comp (continuous_const.prodMk continuous_id)).comp_continuousOn (hU.2.2 v)
  have hae : AEStronglyMeasurable (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ) μ :=
    SmoothA.aesm_of_contOn hμ.conc hc
  rw [memLp_two_iff_integrable_sq_norm hae]
  refine ((hF v w v w).1.re).congr (Filter.Eventually.of_forall fun g => ?_)
  show (⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w, σ (Matrix.of g) v⟫_ℂ).re = ‖⟪w, σ (Matrix.of g) v⟫_ℂ‖ ^ 2
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem frame_blockW_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g)
    {h : Matrix (Fin k) (Fin k) ℂ} (hu : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g * Formalism.MainNotions.S.blockW k r h * g⁻¹ ∈ UWset k r z := by
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  have hdet : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hgU
  have hig : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  have hu' : hᴴ * h = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hu
    simpa [Matrix.star_eq_conjTranspose] using this
  have hBU : Formalism.MainNotions.S.blockW k r h ∈ UH (Hpk k r) := by
    show (Formalism.MainNotions.S.blockW k r h)ᴴ * Hpk k r * Formalism.MainNotions.S.blockW k r h = Hpk k r
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.blockW_conjTranspose, Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.H_comm, ← Matrix.mul_assoc,
      ← ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.blockW_mul, hu', ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.blockW_one, Matrix.one_mul]
  have hfix : ∀ i : Fin (2 * r + k + 1), ¬ ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bl k r i →
      Formalism.MainNotions.S.blockW k r h *ᵥ bvec i = bvec i := by
    intro i hi
    funext j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bw_col h j hi]
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ, Formalism.MainNotions.S.blockW k r h *ᵥ v = v →
      (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) *ᵥ (g *ᵥ v) = g *ᵥ v := by
    intro v hv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (g * _), hig, Matrix.mul_one, ← Matrix.mulVec_mulVec, hv]
  refine ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hgU hBU) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hgU),
    fun a => ⟨?_, ?_⟩, ?_⟩
  · have h1 := key _ (hfix (eI k r a) (by simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bl, eI]; omega))
    rwa [(hgfix a).1] at h1
  · have h1 := key _ (hfix (esI k r a) (by simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bl, esI]; omega))
    rwa [(hgfix a).2] at h1
  · have hw : ¬ ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bl k r (wI k r (Fin.last k)) := by simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding.bl, wI, Fin.val_last]; omega
    have h1 := key (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))
      (by rw [Matrix.mulVec_smul, hfix _ hw])
    rwa [hgz] at h1

theorem pi_facts {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} (hz : inWb k r z)
    (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) :
    IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z) ∧
      Formalism.MainNotions.S.IsIrredOn (UWset k r z) π := by
  obtain ⟨hrep, hiso, hcont⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.hcTypeW_uRep k r z u Vp π hz hT hπ
  refine ⟨hrep, hiso, continuousOn_clm_apply.2 hcont, ?_⟩
  obtain ⟨g, hg, hρ⟩ := hπ
  intro S hS hst
  have hK := hρ.2.2.2.2.2.1 S le_top fun h hh v hv => hst _ (frame_blockW_mem hg hh.1) v hv
  rcases hK with h | h
  · exact Or.inl h
  · exact Or.inr h

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopTA
