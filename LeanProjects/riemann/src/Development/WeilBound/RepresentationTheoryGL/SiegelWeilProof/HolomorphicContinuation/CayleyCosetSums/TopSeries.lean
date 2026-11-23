import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IntegralTsumSupp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

private theorem isCompact_KR' (n : ℕ) : IsCompact ((KR n : Set (GR n))) := by
  classical
  let S : Set (M2 n) := {x | InG x ∧ xᴴ * x = 1}
  have hSc : IsClosed S := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq
        (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hBox : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hSsub : S ⊆ (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) := by
    intro x hx i _ j _
    have hu : x ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hx.2
    simpa using entry_norm_bound_of_unitary hu i j
  have hS : IsCompact S := hBox.of_isClosed_subset hSc hSsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ : S → GR n := fun x =>
    ⟨⟨x.1, x.1ᴴ, mul_eq_one_comm.mp x.2.2, x.2.2⟩, x.2.1⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    exact continuous_subtype_val.matrix_conjTranspose
  have hR : (KR n : Set (GR n)) = Set.range φ := by
    ext Y
    constructor
    · intro hY
      refine ⟨⟨mR Y, hY⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨x, rfl⟩
      exact x.2
  rw [hR]
  exact isCompact_range hφ

theorem topSeries (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) [MeasurableSpace (KR n)] [BorelSpace (KR n)]
    (μ : Measure (KR n)) [IsFiniteMeasure μ] {z : ℂ} (hz : t < z.re) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (hρ : Continuous ρ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (ha : InG a) (hb : InG b) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y))) ∧
    tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y) =
      d.eval z * ∑' q, C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y)) := by
  classical
  haveI : CompactSpace (KR n) := isCompact_iff_compactSpace.mp (isCompact_KR' n)
  set A : GR n := grOf a ha with hA
  set B : GR n := grOf b hb with hB
  have hmul : ∀ Y₁ Y₂ : GR n, mR (Y₁ * Y₂) = mR Y₁ * mR Y₂ := fun _ _ => by simp [mR]
  have hY : ∀ (w : GR n) (k : KR n) (s : Fin n → Fin n → ℝ),
      mR w * ιK n k * a * nU (herm s) * b = mR (w * ((k : GR n) * A * nG s * B)) := by
    intro w k s
    simp only [hmul, ιK_apply, mR_nG, hA, hB, mR_grOf, mul_assoc]
  obtain ⟨hbd, hE⟩ := h.far z hz
  let P : KR n × (Fin n → Fin n → ℝ) → G := fun p => g * ι (y * ((p.1 : GR n) * A * nG p.2 * B))
  have hWc : Continuous fun p : KR n × (Fin n → Fin n → ℝ) => (p.1 : GR n) * A * nG p.2 * B :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_nG.comp continuous_snd)).mul continuous_const
  have hP : Continuous P := continuous_const.mul (h.ιc.comp (continuous_const.mul hWc))
  have hKc : IsCompact (P '' (Set.univ ×ˢ tsupport ψ)) := (isCompact_univ.prod hψc).image hP
  obtain ⟨u, hu, hub⟩ := hbd _ hKc
  have hterm : ∀ q (Y : GR n), GlobalTheory.Eis.term Pp Γ (fun x : G => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) (g * ι Y) q =
      C q * fz m e (z - s₀) (mR (y₀ q * Y)) := by
    intro q Y
    rw [← hyC q Y]
    simp only [GlobalTheory.Eis.term, trm, mul_assoc]
  have hBd : ∀ q (k : KR n) s, s ∈ tsupport ψ →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ |u q| := by
    intro q k s hs
    have h1 := hub (P (k, s)) ⟨(k, s), ⟨Set.mem_univ _, hs⟩, rfl⟩ q
    rw [hterm] at h1
    exact h1.trans (le_abs_self _)
  have hG : ∀ q, Continuous fun p : KR n × (Fin n → Fin n → ℝ) =>
      fz m e (z - s₀) (mR (y₀ q * (y * ((p.1 : GR n) * A * nG p.2 * B)))) := fun q =>
    (continuous_fzG (m := m) (e := e) hS (z - s₀)).comp (continuous_const.mul (continuous_const.mul hWc))
  have hfun : ∀ q (k : KR n) s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) =
      fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B)))) := by
    intro q k s
    rw [hY, mul_assoc]
  have hM : ∀ q, ∃ M : ℝ, ∀ (k : KR n) s, s ∈ tsupport ψ →
      ‖fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ M := by
    intro q
    obtain ⟨M, hM⟩ := (isCompact_univ.prod hψc).exists_bound_of_continuousOn (hG q).continuousOn
    exact ⟨M, fun k s hs => hM (k, s) ⟨Set.mem_univ _, hs⟩⟩
  have hψi : Integrable (fun s => ‖ψ s‖) := (hψ.integrable_of_hasCompactSupport hψc).norm
  have hzero : ∀ s, s ∉ tsupport ψ → ψ s = 0 := fun s hs => image_eq_zero_of_notMem_tsupport hs
  have hIc : ∀ q, Continuous fun k : KR n =>
      ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s := by
    intro q
    obtain ⟨M, hMb⟩ := hM q
    simp_rw [hfun]
    refine continuous_of_dominated (bound := fun s => M * ‖ψ s‖) ?_ ?_ (hψi.const_mul M) ?_
    · intro k
      exact (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ).aestronglyMeasurable
    · intro k
      refine Filter.Eventually.of_forall fun s => ?_
      by_cases hs : s ∈ tsupport ψ
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hMb k s hs) (norm_nonneg _)
      · simp [hzero s hs]
    · refine Filter.Eventually.of_forall fun s => ?_
      exact ((hG q).comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hv : Summable fun q => |u q| := hu.abs
  have hv0 : ∀ q, 0 ≤ |u q| := fun q => abs_nonneg _
  have hFb : ∀ q (k : KR n) s,
      ‖C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤ |u q| * ‖ψ s‖ := by
    intro q k s
    rw [hfun, ← mul_assoc, norm_mul]
    by_cases hs : s ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hBd q k s hs) (norm_nonneg _)
    · simp [hzero s hs]
  have hin : ∀ k : KR n,
      (Summable fun q => ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)) ∧
      ∫ s, ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) =
        ∑' q, ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k
    refine integral_tsum_supp _ (fun q => |u q|) hv hv0 (fun s => ‖ψ s‖) hψi (fun q s => hFb q k s) ?_
    intro q
    simp_rw [hfun]
    exact (continuous_const.mul
      (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ)).aestronglyMeasurable
  have hIb : ∀ q (k : KR n),
      ‖C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by
    intro q k
    have h2 : ‖∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        ∫ s, |u q| * ‖ψ s‖ :=
      norm_integral_le_of_norm_le (hψi.const_mul _) (Filter.Eventually.of_forall fun s => hFb q k s)
    rw [integral_const_mul] at h2
    rw [integral_const_mul] at h2
    rw [mul_left_comm, norm_mul, norm_mul]
    rw [norm_mul] at h2
    calc ‖ρ k‖ * (‖C q‖ * ‖∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s‖)
        ≤ ‖ρ k‖ * (|u q| * ∫ s, ‖ψ s‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by ring
  have hbdρ : Integrable (fun k : KR n => ‖ρ k‖ * ∫ s, ‖ψ s‖) μ :=
    (hρ.norm.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hout := integral_tsum_supp (ν := μ)
    (fun q k => C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s))
    (fun q => |u q|) hv hv0 _ hbdρ hIb
    (fun q => (continuous_const.mul (hρ.mul (hIc q))).aestronglyMeasurable)
  have hpt : ∀ (k : KR n) s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
      d.eval z * ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k s
    rw [hY, resG_mR, hE, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfun, ← mul_assoc (C q), ← hyC q]
    simp only [trm, mul_assoc]
  refine ⟨?_, ?_⟩
  · refine hout.1.congr fun q => ?_
    simp only [tOp, integral_const_mul]
  · have hL : ∀ k : KR n, ρ k * ∫ s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
        d.eval z * ∑' q, C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
      intro k
      simp_rw [hpt k]
      rw [integral_const_mul, (hin k).2]
      simp_rw [integral_const_mul]
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      refine tsum_congr fun q => ?_
      ring
    simp only [tOp]
    simp_rw [hL]
    rw [integral_const_mul, hout.2]
    congr 1
    refine tsum_congr fun q => ?_
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.FarP
