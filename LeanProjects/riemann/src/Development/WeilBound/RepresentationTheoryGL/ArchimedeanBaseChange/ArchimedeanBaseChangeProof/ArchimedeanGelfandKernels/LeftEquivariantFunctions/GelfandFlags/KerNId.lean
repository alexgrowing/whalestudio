import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNIdC

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC KN
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem integrable_of_continuousOn_of_eq_zero_lg_gt (hLg : LgCpt) {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] {X : Type} [NormedAddCommGroup X]
    (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ)
    (hR : ∀ y ∈ GLs n, R < lg y → h y = 0) :
    Integrable (fun y : G n => h ↑y) μ := by
  have hcont : Continuous (fun y : G n => h ↑y) :=
    hc.comp_continuous Units.continuous_val (fun y => KN.memGL y)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hLg n R) ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ (KN.memGL y) hy

theorem kerNId_of' (hLg : LgCpt) : KerNId := by
  intro hNil hKZ hAvg n i1 i2 μ i3 E k hk hsupp hequi W₁ W₂ hW N hN ν i4 A hA hQ hcomm y hy
  obtain ⟨hNc, hInv⟩ := hNil n W₁ W₂ hW N hN
  haveI := hInv ν
  obtain ⟨Rk, hRk⟩ := hsupp
  have hkc : ContinuousOn k (GLs n) := hk.continuousOn
  have hAc : ContinuousOn A (GLs n) := hA.1.continuousOn
  obtain ⟨K, hK⟩ : ∃ K : Mat n → E.V →L[ℂ] E.V,
      K = fun x => ∫ u : N, k (((u : G n) : Mat n) * x) ∂ν := ⟨_, rfl⟩
  have hKapp : ∀ x, (∫ u : N, k (((u : G n) : Mat n) * x) ∂ν) = K x := fun x => by rw [hK]
  have hKc : ContinuousOn K (GLs n) := by
    rw [hK]
    exact KN.contOn_avg hLg hNc ν k hkc Rk hRk
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hKr : ∀ x ∈ GLs n, ∀ c : unitaryGroup (Fin n) ℂ, K (x * ↑c) = K x * E.ρ c := by
    intro x hx c
    have hint := KN.integrable_N hLg hNc ν k hkc Rk hRk x hx
    rw [← hKapp, ← hKapp]
    have e : ∀ u : N, k (((u : G n) : Mat n) * (x * (c : Mat n))) =
        k (((u : G n) : Mat n) * x) * E.ρ c := by
      intro u
      have := hequi (((u : G n) : Mat n) * x) (KN.mul_memGL _ x hx) 1 c
      simpa [mul_assoc] using this
    simp_rw [e]
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ c)).integral_comp_comm hint
  have hκc : ContinuousOn (fun x => K x * A x - A 1 * K x) (GLs n) :=
    (hKc.mul hAc).sub (continuousOn_const.mul hKc)
  have hρ : ∀ c : unitaryGroup (Fin n) ℂ, E.ρ c * E.ρ c⁻¹ = 1 := fun c => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hκr : ∀ x ∈ GLs n, ∀ c : unitaryGroup (Fin n) ℂ,
      K (x * ↑c) * A (x * ↑c) - A 1 * K (x * ↑c) = (K x * A x - A 1 * K x) * E.ρ c := by
    intro x hx c
    rw [hKr x hx c, hA.2 x hx c, sub_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (E.ρ c) (E.ρ c⁻¹), hρ, one_mul]
  have hκi : ∀ f ∈ CE E, (∃ R : ℝ, ∀ x ∈ GLs n, R < lg x → f x = 0) →
      ∫ x : G n, (K ↑x * A ↑x - A 1 * K ↑x) (f ↑x) ∂μ = 0 := by
    rintro f hf ⟨Rf, hRf⟩
    have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
    have hF := hAvg n E W₁ W₂ hW N hN ν f hf ⟨Rf, hRf⟩
    have hBinv : ∀ (u : N), ∀ x ∈ GLs n, A (((u : G n) : Mat n) * x) = A x := fun u x hx =>
      hQ _ (KN.memGL _) (KN.maps_of hW hN u).1 (KN.maps_of hW hN u).2 x hx
    have k1 := KN.key hLg μ E k A hkc Rk hRk hNc ν hAc hBinv f hfc Rf hRf
    have k2 := KN.key hLg μ E k (fun _ => 1) hkc Rk hRk hNc ν continuousOn_const
      (fun _ _ _ => rfl) f hfc Rf hRf
    have hc := hcomm _ hF.1 hF.2 1 h1
    simp only [act, one_mul] at hc
    simp only [ContinuousLinearMap.one_apply] at k2
    simp only [hKapp] at k1 k2
    have I1 : Integrable (fun x : G n => K ↑x (A ↑x (f ↑x))) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => K x (A x (f x)))
        (hKc.clm_apply (hAc.clm_apply hfc)) Rf (fun x hx h => by simp [hRf x hx h])
    have I2 : Integrable (fun x : G n => A 1 (K ↑x (f ↑x))) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => A 1 (K x (f x)))
        ((A 1).continuous.comp_continuousOn (hKc.clm_apply hfc)) Rf
        (fun x hx h => by simp [hRf x hx h])
    have I3 : Integrable (fun x : G n => K ↑x (f ↑x)) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => K x (f x)) (hKc.clm_apply hfc) Rf
        (fun x hx h => by simp [hRf x hx h])
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
    rw [integral_sub I1 I2, (A 1).integral_comp_comm I3, ← k1, ← k2, hc, sub_self]
  have hκ : K y * A y - A 1 * K y = 0 :=
    hKZ n μ E (fun x => K x * A x - A 1 * K x) hκc hκr hκi y hy
  rw [hKapp]
  exact sub_eq_zero.mp hκ

theorem kerNId_of (hLg : LgCpt) (_ : IntSmooth) : KerNId := kerNId_of' hLg

end PositivityTheory.RgBcC.VC
