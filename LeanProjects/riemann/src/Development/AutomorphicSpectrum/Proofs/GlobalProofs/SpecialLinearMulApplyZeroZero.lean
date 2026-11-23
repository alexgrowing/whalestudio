import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
open MeasureTheory Topology Set Filter CompanionTheory.D.gk.admitted.Gard

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Op

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_avg_op (ρ : Γ → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : Γ → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ i : tsupport w, ‖ρ i‖ ≤ C := by
    refine banach_steinhaus (g := fun i : tsupport w => ρ i) fun u => ?_
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := tsupport w) hc (hρ u).continuousOn
    exact ⟨C, fun i => hC i i.2⟩
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  have hwi : Integrable (fun x => ‖w x‖) μ := (hw.integrable_of_hasCompactSupport hc).norm
  refine ⟨L.mkContinuous ((∫ x, ‖w x‖ ∂μ) * C) fun u => ?_, fun u => rfl⟩
  have hb : ‖∫ x, w x • ρ x u ∂μ‖ ≤ ∫ x, ‖w x‖ * (C * ‖u‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul]
    by_cases hx : w x = 0
    · simp [hx]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact ((ρ x).le_opNorm u).trans (mul_le_mul_of_nonneg_right
        (hC ⟨x, subset_tsupport _ hx⟩) (norm_nonneg _))
  rw [integral_mul_const] at hb
  rw [mul_assoc]
  exact hb

end Op

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def GT (_ : IsLinRed G) (_ : IsClosed G) : Type := {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G}

variable {hG : IsLinRed G} {hcl : IsClosed G}

def toM (x : GT hG hcl) : Matrix (Fin n) (Fin n) ℂ := x.1

theorem det_unit (x : GT hG hcl) : IsUnit (toM x).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (hG.isUnit _ x.2)

instance : Mul (GT hG hcl) := ⟨fun x y => ⟨x.1 * y.1, hG.mul_mem _ x.2 _ y.2⟩⟩

instance : One (GT hG hcl) := ⟨⟨1, hG.one_mem⟩⟩

instance : Inv (GT hG hcl) := ⟨fun x => ⟨x.1⁻¹, hG.inv_mem _ x.2⟩⟩

instance : Group (GT hG hcl) :=
  Group.ofLeftAxioms (fun x y z => Subtype.ext (Matrix.mul_assoc x.1 y.1 z.1))
    (fun x => Subtype.ext (Matrix.one_mul x.1))
    (fun x => Subtype.ext (Matrix.nonsing_inv_mul x.1 (det_unit x)))

theorem toM_mul (x y : GT hG hcl) : toM (x * y) = toM x * toM y := rfl

theorem toM_one : toM (1 : GT hG hcl) = 1 := rfl

instance : TopologicalSpace (GT hG hcl) := inferInstanceAs (TopologicalSpace {g // g ∈ G})

instance : T2Space (GT hG hcl) := inferInstanceAs (T2Space {g // g ∈ G})

instance : SecondCountableTopology (GT hG hcl) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  inferInstanceAs (SecondCountableTopology {g // g ∈ G})

theorem emb_toM : IsClosedEmbedding (toM : GT hG hcl → Matrix (Fin n) (Fin n) ℂ) :=
  hcl.isClosedEmbedding_subtypeVal

instance : LocallyCompactSpace (GT hG hcl) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  emb_toM.locallyCompactSpace

instance : IsTopologicalGroup (GT hG hcl) where
  continuous_mul := by
    rw [emb_toM.isInducing.continuous_iff]
    exact (emb_toM.continuous.comp continuous_fst).mul (emb_toM.continuous.comp continuous_snd)
  continuous_inv := by
    rw [emb_toM.isInducing.continuous_iff]
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (toM x) := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (det_unit x).ne_zero
    exact h1.comp emb_toM.continuous.continuousAt

instance : MeasurableSpace (GT hG hcl) := borel _

instance : BorelSpace (GT hG hcl) := ⟨rfl⟩

theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) : ∃ x : GT hG hcl, toM x = g := ⟨⟨g, hg⟩, rfl⟩

theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (GT hG hcl), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure (GT hG hcl)) [IsFiniteMeasureOnCompacts μ]
    (v : GT hG hcl → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ}
    {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : GT hG hcl, f (toM x⁻¹ * g) • v x ∂μ := by
  have hq : Continuous fun x : GT hG hcl => (toM x⁻¹, v x) :=
    (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp μ _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (hG := hG) (hcl := hcl) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

theorem toM_inv_of_unitary {k : GT hG hcl} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    toM k⁻¹ = (toM k)ᴴ :=
  Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 hk)

theorem smooth_of_commutant_stable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    (hK : ∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y]
    (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u)) → ∀ y ∈ Y, T y ∈ Y) :
    ∀ v ∈ Y, IsSmoothVec G π v := by
  intro v hv
  let μ : Measure (GT hG hcl) := Measure.haar
  obtain ⟨h1, hm⟩ := hrep
  let ρ : GT hG hcl → H →L[ℂ] H := fun x => π (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hc u).comp_continuous emb_toM.continuous fun x => x.2
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    show π (toM x * toM y) u = π (toM x) (π (toM y) u)
    rw [hm (toM x) x.2 (toM y) y.2, ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, ContinuousLinearMap.one_apply]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : GT hG hcl) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : GT hG hcl → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hcw : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_avg_op μ ρ hρ hw hcw
  have hTK : ∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (hG := hG) (hcl := hcl) hk.1
    rw [hT, hT]
    refine T_comm μ ρ hρ hmul hw hcw h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.2, hfk _ hk.2]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt μ ρ hρ hw hcw h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  have hF := contDiff_avg μ (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS
  refine ⟨fun z => ∫ x : GT hG hcl, f (toM x⁻¹ * Matrix.of z) • ρ x u ∂μ, hF, fun z hz => ?_⟩
  obtain ⟨g', hg'⟩ := exists_toM (hG := hG) (hcl := hcl) hz
  show π (Matrix.of z) (T u) = ∫ x : GT hG hcl, f (toM x⁻¹ * Matrix.of z) • ρ x u ∂μ
  rw [← hg']
  show ρ g' (T u) = _
  rw [hT, apply_alt μ ρ hρ hmul hw hcw]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

section ClosedNeeded

def gl1 : Set (Matrix (Fin 1) (Fin 1) ℂ) := {g | g 0 0 ≠ 0}

def phase (g : Matrix (Fin 1) (Fin 1) ℂ) : ℂ →L[ℂ] ℂ := (g 0 0 / (‖g 0 0‖ : ℂ)) • (1 : ℂ →L[ℂ] ℂ)

end ClosedNeeded

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard

end
