import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsIsotypicSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SpecialLinearMulApplyZeroZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PolyGrowthOfIsometricOnK
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RpowNegLeOfDichotomy
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AlmostIsomOfGrowth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitaryIwasawaLeviOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SecondCountableGrp
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsBasisLieOfOrthogonal
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SumSquaresComm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticOnUJOfWordBound
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IterateRealSmul

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem isotypic : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic.exists_isotypic_sum

theorem garding : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hK : ∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u)) → ∀ y ∈ Y, T y ∈ Y), ∀ v ∈ Y, IsSmoothVec G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard.smooth_of_commutant_stable

theorem growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hK : ∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖), ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth.polyGrowth_of_isometric_on_K

theorem volume : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume.integrable_wt_rpow_neg

theorem almost_of_growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hg : ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖) (hv : ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv), AlmostIsom (UJset ε) π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Growth.almostIsom_of_growth

theorem iwa_levi : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W), g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi.exists_unitary_iwasawa_leviOne

theorem admissible_of_iwasawa_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) (hU : IsURepOn G π) (hirr : IsIrredOn G π), IsAdmOn G π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted.isAdmOn_of_iwasawa

theorem smooth_deriv : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec

theorem smooth_lin : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear

theorem inv_basis : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal

theorem delta_comm : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G) (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l) {v : H} (hv : IsSmoothVec G π v), π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.sumSquares_comm

theorem word_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta.word_bound_of_delta

theorem analytic_uj : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H} (hs : IsSmoothVec (UJset ε) π v) (hw : WordBound (UJset ε) π v) (w : H), GlobalTheory.Published.AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.AnalyticWords.analyticOnUJ_of_wordBound

theorem one_param : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H), AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam.analytic_coeff

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_word_of_adm {G : Set (Matrix (Fin n) (Fin n) ℂ)} [CompleteSpace H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hA : IsAdmOn G π) (hQ : AlmostIsom G π) {v : H}
    (hv : IsKFinOn G π v) : IsSmoothVec G π v ∧ WordBound G π v := by
  obtain ⟨hrep, hc, hK, -⟩ := id hA
  obtain ⟨Y, hYf, hvY, hYK, hD⟩ := isotypic hG hA hv
  have hYs : ∀ y ∈ Y, IsSmoothVec G π y := garding hG hcl hrep hc hK Y fun T hT y hy => by
    have := hD ((T : H →ₗ[ℂ] H).comp Y.subtype) (fun k hk y y' e => by
      show T (y' : H) = π k (T (y : H))
      rw [e, hT k hk]) ⟨y, hy⟩
    exact this
  obtain ⟨d, b, hb, hli, hsp, hinv⟩ := inv_basis hG
  refine ⟨hYs v hvY, word_of_delta hG hrep hc hQ b hb hli hsp Y hYs ?_ v hvY⟩
  have hsm : ∀ (y : H), IsSmoothVec G π y → ∀ i, IsSmoothVec G π (dRep π (b i) (dRep π (b i) y)) := fun y hy i =>
    (smooth_deriv hG hrep (smooth_deriv hG hrep hy (hb i)).2 (hb i)).2
  let Dl : Y →ₗ[ℂ] H :=
    { toFun := fun y => ∑ i, dRep π (b i) (dRep π (b i) (y : H))
      map_add' := fun x y => by
        refine Finset.sum_congr rfl (fun i _ => ?_) |>.trans Finset.sum_add_distrib
        have hx := hYs x x.2
        have hy := hYs y y.2
        rw [Submodule.coe_add, (smooth_lin hG hrep hx hy (hb i) (hb i)).2.1,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hy (hb i)).2
            (hb i) (hb i)).2.1]
      map_smul' := fun c x => by
        have hx := hYs x x.2
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, (smooth_lin hG hrep hx hx (hb i) (hb i)).2.2,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hx (hb i)).2
            (hb i) (hb i)).2.2] }
  intro y hy
  refine hD Dl (fun k hk y y' e => ?_) ⟨y, hy⟩
  obtain ⟨O, hO, hkb⟩ := hinv k hk
  show ∑ i, dRep π (b i) (dRep π (b i) (y' : H)) = π k (∑ i, dRep π (b i) (dRep π (b i) (y : H)))
  rw [e, delta_comm hG hrep b hb hk.1 O hO hkb (hYs y y.2)]

theorem isClosed_UJset (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem almostIsom_of_unitary {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn G π) : AlmostIsom G π := by
  refine ⟨fun x y => ⟪x, y⟫_ℂ, 1, 1, 0, one_pos, zero_le_one, le_refl _, fun x y z => inner_add_right x y z,
    fun c x y => inner_smul_right x y c, fun x y => (inner_conj_symm y x).symm, fun x => ?_, fun x y => ?_,
    fun X hX t x => ?_⟩
  · show 1 * ‖x‖ ^ 2 ≤ (⟪x, x⟫_ℂ).re
    rw [one_mul, inner_self_eq_norm_sq_to_K]; norm_cast
  · show ‖⟪x, y⟫_ℂ‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [one_mul]; exact norm_inner_le_norm x y
  · have h : ∀ u : H, (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := fun u => by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    show (⟪π _ x, π _ x⟫_ℂ).re ≤ _ * (⟪x, x⟫_ℂ).re
    simp only [h, hU.2.1 _ (hX t) x]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open HCA

theorem admissibleCoefficientsAnalytic : GlobalTheory.Published.AdmissibleCoefficientsAnalytic := by
  intro n ε H _ _ _ π hπ v w hv _
  have hG := GlobalTheory.HCUnitary.isLinRed_UJset ε
  have hA : IsAdmOn (UJset ε) π := GlobalTheory.HCUnitary.isAdmOn_iff.2 hπ
  have hQ : AlmostIsom (UJset ε) π :=
    almost_of_growth hπ.1 hπ.2.1 (growth hπ.1 hπ.2.1 hπ.2.2.1) (volume ε)
  have hv' : IsKFinOn (UJset ε) π v := by
    obtain ⟨S, h1, h2, h3⟩ := hv
    exact ⟨S, h1, h2, GlobalTheory.HCUnitary.isKStable_iff.2 h3⟩
  obtain ⟨hs, hw⟩ := smooth_word_of_adm hG (isClosed_UJset ε) hA hQ hv'
  exact analytic_uj hπ.1 hπ.2.1 hs hw w

theorem leviSubmoduleDense : GlobalTheory.Published.LeviSubmoduleDense := by
  intro n ε a j W hW hj V _ _ _ σ hU hI S hS hK hL
  obtain ⟨hG, hexp⟩ := GlobalTheory.LeviPolar.isLinRed_leviOne n ε a j W hW hj
  have hA : IsAdmOn (mats (leviOne ε W)) σ := admissible_of_iwasawa_decomposition hG (iwa_levi hW hj) hU hI
  have hQ := almostIsom_of_unitary hU
  have hcl : IsClosed (mats (leviOne ε W)) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isClosedMap _ (isClosed_leviOne hW hj)
  have keep : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
      ∀ v ∈ S.topologicalClosure, σ (NormedSpace.exp X) v ∈ S.topologicalClosure := fun X hX => by
    have := GlobalTheory.LeviDense.oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) (by simp [hU.1.1])
      (fun s t => by
        rw [← hU.1.2 _ (hX s) _ (hX t), add_smul,
          Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
      (hL X hX)
      (fun v hv w => by
        obtain ⟨h1, h2⟩ := smooth_word_of_adm hG hcl hA hQ (GlobalTheory.LeviDense.isKFinOn_of_isKFinIn (hK v hv))
        exact one_param hG hU h1 h2 hX w) 1
    simpa only [one_smul] using this
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure (fun g hg v hv => by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hexp g hg
    rw [hU.1.2 _ (by simpa using hX 1) _ (by simpa using hY 1)]
    exact keep X hX _ (keep Y hY v hv)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ S.le_topologicalClosure)) hS
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem harishChandra_analyticity_density : GlobalTheory.Published.HarishChandraAnalyticity :=
  ⟨admissibleCoefficientsAnalytic, leviSubmoduleDense⟩

end GlobalTheory.CompanionTheory.Hypotheses₂

end
