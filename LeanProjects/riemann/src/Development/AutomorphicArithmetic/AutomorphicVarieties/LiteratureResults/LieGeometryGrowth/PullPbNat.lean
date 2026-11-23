import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth

open UpperTheory.V.Lit.Geo
open scoped ContDiff

private theorem pbNat_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y)
    (ρ : V →L[ℝ] V) {W W' : V → V} (hW : IsField Y W) (hW' : IsField Y W') (hρ : ∀ p ∈ Y, ρ p ∈ Y)
    (he : ∀ p ∈ Y, W' (ρ p) = ρ (W p)) (t : ℝ) {p : V} (hp : p ∈ Y) :
    flow W' t (ρ p) = ρ (flow W t p) ∧ ∀ v, fderiv ℝ (flow W' t) (ρ p) (ρ v) = ρ (fderiv ℝ (flow W t) p v) := by
  have hd : ∀ (U : V → V) (x : V), DifferentiableAt ℝ U x → ∀ v : V,
      fderiv ℝ (flow U t) x v = v + t • fderiv ℝ U x v := by
    intro U x hU v
    have h := (hasFDerivAt_id x).add (hU.hasFDerivAt.const_smul t)
    have hfl : flow U t = id + t • U := by
      funext y
      simp [flow]
    rw [hfl, h.fderiv]
    simp
  constructor
  · simp only [flow]
    rw [he p hp]
    simp [map_add, map_smul]
  · intro v
    have hWd : DifferentiableAt ℝ W p :=
      (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
    have hW'd : DifferentiableAt ℝ W' (ρ p) :=
      (hW'.1.contDiffAt (hY.mem_nhds (hρ p hp))).differentiableAt (by simp)
    have heq : (fun x => W' (ρ x)) =ᶠ[nhds p] (fun x => ρ (W x)) := by
      filter_upwards [hY.mem_nhds hp] with x hx using he x hx
    have hder : fderiv ℝ W' (ρ p) (ρ v) = ρ (fderiv ℝ W p v) := by
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      have c1 : fderiv ℝ (fun x => W' (ρ x)) p = (fderiv ℝ W' (ρ p)).comp ρ :=
        (hW'd.hasFDerivAt.comp p ρ.hasFDerivAt).fderiv
      have c2 : fderiv ℝ (fun x => ρ (W x)) p = ρ.comp (fderiv ℝ W p) :=
        (ρ.hasFDerivAt.comp p hWd.hasFDerivAt).fderiv
      have h3 := congrArg (fun L => L v) (c1.symm.trans (h1.trans c2))
      simpa using h3
    rw [hd W' (ρ p) hW'd, hd W p hWd, hder]
    simp [map_add, map_smul]

theorem UpperTheory.V.Lit.Geo.pbNat :
    PbNat := by
  unfold PbNat
  intro V F _ _ _ _ _ _ Y hY ρ A W W' hW hW' hρ he q
  constructor
  · intro w w' hww t ht p hp v
    obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
    rw [pb_apply, pb_apply, h1]
    simp only [h2]
    exact hww _ (hW.2 p hp t ht) _
  · intro w w' hww
    have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v : Fin q → V,
        (hk W' t w' (ρ p)) (fun i => ρ (v i)) = A ((hk W t w p) v) := by
      intro t ht p hp v
      obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
      rw [hk_apply, hk_apply, h1, he p hp]
      simp only [h2]
      convert hww (flow W t p) (hW.2 p hp t ht)
        (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) using 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    refine ⟨hb1, fun hwc hw'c p hp v => ?_⟩
    have hk1 := (hkSmooth V F Y hY W hW q w hwc).2.2.1 p hp
    have hk2 := (hkSmooth V F Y hY W' hW' q w' hw'c).2.2.1 (ρ p) (hρ p hp)
    have i1 : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk1
    have i2 : IntervalIntegrable (fun t => hk W' t w' (ρ p)) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk2
    have i3 : IntervalIntegrable (fun t => (hk W t w p) v) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (ContinuousAlternatingMap.apply ℝ V F v).continuous.comp_continuousOn hk1
    have e1 : (∫ t in (0 : ℝ)..1, hk W' t w' (ρ p)) (fun i => ρ (v i)) =
        ∫ t in (0 : ℝ)..1, (hk W' t w' (ρ p)) (fun i => ρ (v i)) :=
      ((ContinuousAlternatingMap.apply ℝ V F (fun i => ρ (v i))).intervalIntegral_comp_comm i2).symm
    have e2 : (∫ t in (0 : ℝ)..1, hk W t w p) v = ∫ t in (0 : ℝ)..1, (hk W t w p) v :=
      ((ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm i1).symm
    unfold hom
    rw [e1, e2, ← A.intervalIntegral_comp_comm i3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hb1 t ht p hp v
