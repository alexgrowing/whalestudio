import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsPowerUnitCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix Polynomial

noncomputable section

theorem encard_pow_eq_of_ne_zero {m : ℕ} (hm : m ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    {a : ℂ | a ^ m = t}.encard = m := by
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hset : {a : ℂ | a ^ m = t} = ↑(nthRootsFinset m t) := by
    ext a
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hm)]
  classical
  rw [hset, Set.encard_coe_eq_coe_finsetCard, nthRootsFinset_def,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ht), hζ.card_nthRoots,
    if_pos ⟨t ^ ((m : ℂ)⁻¹), Complex.cpow_nat_inv_pow t hm⟩]

theorem powerUnitCount_of_root {d m : ℕ} {F : (Fin (d + 1) → ℂ) → Fin d → ℂ}
    {H k : (Fin (d + 1) → ℂ) → ℂ} {s : Fin (d + 1) → ℂ} (hs0 : s 0 = 0)
    (hF : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s) (hHc : ContinuousAt H s) (hHs : H s ≠ 0)
    (hk : AnalyticAt ℂ k s) (hks : k s ≠ 0) (hkm : m ≠ 0 → ∀ τ, k τ ^ m = H τ)
    (hbij : Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s)) :
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m := by
  set Ψ : (Fin (d + 1) → ℂ) → Fin (d + 1) → ℂ := fun τ => vecCons (τ 0) (F τ) with hΨ
  set Φ : (Fin (d + 1) → ℂ) → Fin (d + 1) → ℂ := fun τ => vecCons (τ 0 * k τ) (F τ) with hΦ
  have h0 : AnalyticAt ℂ (fun τ : Fin (d + 1) → ℂ => τ 0) s :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt s
  have hΨa : AnalyticAt ℂ Ψ s := by
    refine (analyticAt_pi_iff (f := fun i τ => Ψ τ i)).mpr fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hΨ] using h0
    · simpa [hΨ] using hF j
  have hΦa : AnalyticAt ℂ Φ s := by
    refine (analyticAt_pi_iff (f := fun i τ => Φ τ i)).mpr fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · show AnalyticAt ℂ (fun τ => τ 0 * k τ) s
      exact h0.mul hk
    · simpa [hΦ] using hF j
  have hΨd : HasFDerivAt Ψ (fderiv ℂ Ψ s) s := hΨa.differentiableAt.hasFDerivAt
  have hΦs : HasStrictFDerivAt Φ (fderiv ℂ Φ s) s := hΦa.hasStrictFDerivAt
  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ s) s := hΦs.hasFDerivAt

  have hΨ0 : ∀ v, fderiv ℂ Ψ s v 0 = v 0 := by
    intro v
    have h1 := hasFDerivAt_pi'.mp hΨd 0
    have h2 : HasFDerivAt (fun τ => Ψ τ 0)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0) s :=
      hasFDerivAt_apply 0 s
    exact DFunLike.congr_fun (h1.unique h2) v
  have hΦ0 : ∀ v, fderiv ℂ Φ s v 0 = k s * v 0 := by
    intro v
    have h1 := hasFDerivAt_pi'.mp hΦd 0
    have h2 : HasFDerivAt (fun τ => Φ τ 0) (s 0 • fderiv ℂ k s +
        k s • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0) s :=
      (hasFDerivAt_apply 0 s).mul hk.differentiableAt.hasFDerivAt
    have h3 := DFunLike.congr_fun (h1.unique h2) v
    simpa [hs0] using h3
  have hsucc : ∀ v (j : Fin d), fderiv ℂ Φ s v j.succ = fderiv ℂ Ψ s v j.succ := by
    intro v j
    have h1 := hasFDerivAt_pi'.mp hΦd j.succ
    have h2 := hasFDerivAt_pi'.mp hΨd j.succ
    exact DFunLike.congr_fun (h1.unique h2) v
  have hinj : Function.Injective (fderiv ℂ Φ s) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply hbij.1
    rw [map_zero]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h1 : fderiv ℂ Φ s v 0 = 0 := by rw [hv]; rfl
      rw [hΦ0] at h1
      rw [hΨ0]
      simpa [hks] using h1
    · have h1 : fderiv ℂ Φ s v j.succ = 0 := by rw [hv]; rfl
      rw [hsucc] at h1
      simpa using h1
  have hsurj : Function.Surjective
      (fderiv ℂ Φ s : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ Φ s : _ →ₗ[ℂ] _) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hΦe : HasStrictFDerivAt Φ (e : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) s := by
    have he : (e : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) = fderiv ℂ Φ s :=
      ContinuousLinearMap.ext fun v => rfl
    rw [he]
    exact hΦs
  obtain ⟨φ, hφ, hsrc⟩ : ∃ φ : OpenPartialHomeomorph (Fin (d + 1) → ℂ) (Fin (d + 1) → ℂ),
      ⇑φ = Φ ∧ s ∈ φ.source :=
    ⟨_, hΦe.toOpenPartialHomeomorph_coe, hΦe.mem_toOpenPartialHomeomorph_source⟩
  have hinjΦ : Set.InjOn Φ φ.source := hφ ▸ φ.injOn
  have hΦzero : ∀ τ, τ 0 = 0 → Φ τ = vecCons 0 (F τ) := by
    intro τ hτ
    simp [hΦ, hτ]
  have hΦk : ∀ τ, m ≠ 0 → τ 0 ^ m * H τ = (τ 0 * k τ) ^ m := by
    intro τ hm
    rw [mul_pow, hkm hm τ]
  refine ⟨φ.source ∩ {τ | ‖H s‖ / 2 < ‖H τ‖}, Filter.inter_mem (φ.open_source.mem_nhds hsrc)
    (hHc.norm.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hHs)))), ?_, ?_⟩
  · rintro τ ⟨⟨hτs, -⟩, hτ0⟩ τ' ⟨⟨hτ's, -⟩, hτ'0⟩ hFF
    apply hinjΦ hτs hτ's
    rw [hΦzero τ hτ0, hΦzero τ' hτ'0, hFF]
  intro P hP hPP
  have hPn : Φ '' P ∈ 𝓝 (vecCons 0 (F s)) := by
    rw [← hΦzero s hs0, ← hφ]
    exact φ.image_mem_nhds hsrc hP
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hPn
  have hpull : ∀ (a : ℂ) (w : Fin d → ℂ), ‖a‖ < ε → w ∈ Metric.ball (F s) ε →
      ∃ τ ∈ P, Φ τ = vecCons a w := by
    intro a w ha hw
    have hmem : vecCons a w ∈ Metric.ball (vecCons 0 (F s)) ε := by
      rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · rw [Metric.mem_ball, dist_eq_norm] at hw
        simpa using (norm_le_pi_norm (w - F s) j).trans_lt hw
    obtain ⟨τ, hτP, hτ⟩ := hball hmem
    exact ⟨τ, hτP, hτ⟩
  refine ⟨Metric.ball (F s) ε, if m = 0 then ‖H s‖ / 2 else ε ^ m, Metric.isOpen_ball,
    Metric.mem_ball_self hε, ?_, ?_, ?_⟩
  · split_ifs
    · exact half_pos (norm_pos_iff.mpr hHs)
    · positivity
  · intro w hw τ hτ hτ0 hFw
    obtain ⟨τ', hτ'P, hτ'⟩ := hpull 0 w (by simpa using hε) hw
    have : τ' = τ := hinjΦ (hPP hτ'P).1 hτ.1 (by rw [hτ', hΦzero τ hτ0, hFw])
    exact this ▸ hτ'P
  · intro w hw t ht0 htρ
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl] at htρ
      have hempty : {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ 0 * H τ = t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro τ ⟨hτP, -, hτt⟩
        have h1 : ‖H s‖ / 2 < ‖H τ‖ := (hPP hτP).2
        rw [pow_zero, one_mul] at hτt
        rw [hτt] at h1
        linarith
      rw [hempty, Set.encard_empty]
      rfl
    rw [if_neg hm] at htρ
    have himg : Φ '' {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t} =
        (fun a => vecCons a w) '' {a : ℂ | a ^ m = t} := by
      ext x
      constructor
      · rintro ⟨τ, ⟨-, hFw, hτt⟩, rfl⟩
        refine ⟨τ 0 * k τ, ?_, ?_⟩
        · show (τ 0 * k τ) ^ m = t
          rw [← hΦk τ hm]
          exact hτt
        · simp [hΦ, hFw]
      · rintro ⟨a, ha, rfl⟩
        have ha' : a ^ m = t := ha
        have hlt : ‖a‖ < ε := by
          refine lt_of_pow_lt_pow_left₀ m hε.le ?_
          rw [← norm_pow, ha']
          exact htρ
        obtain ⟨τ, hτP, hτ⟩ := hpull a w hlt hw
        have h12 := vecCons_inj.mp (show vecCons (τ 0 * k τ) (F τ) = vecCons a w from hτ)
        refine ⟨τ, ⟨hτP, h12.2, ?_⟩, hτ⟩
        rw [hΦk τ hm, h12.1]
        exact ha'
    have hcons : Function.Injective (fun a : ℂ => (vecCons a w : Fin (d + 1) → ℂ)) :=
      fun a b hab => (vecCons_inj.mp hab).1
    rw [← (hinjΦ.mono fun τ hτ => (hPP hτ.1).1).encard_image, himg, hcons.encard_image,
      encard_pow_eq_of_ne_zero hm (norm_pos_iff.mp ht0)]

theorem PowerUnitCount.proof : PowerUnitCount.Statement := by
  intro d m O F H s hO hs hs0 hF hH hHs hbij
  have hFa : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O _ hO (differentiableOn_pi.mp hF j) s hs
  have hHa : AnalyticAt ℂ H s := ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O H hO hH s hs
  by_cases hm : m = 0
  · exact powerUnitCount_of_root (k := fun _ => 1) hs0 hFa hHa.continuousAt hHs analyticAt_const
      one_ne_zero (fun h => (h hm).elim) hbij
  · have hroot : ∀ x : ℂ, (x ^ ((m : ℂ)⁻¹)) ^ m = x := fun x => Complex.cpow_nat_inv_pow x hm
    refine powerUnitCount_of_root (k := fun τ => H s ^ ((m : ℂ)⁻¹) * ((H s)⁻¹ * H τ) ^ ((m : ℂ)⁻¹))
      hs0 hFa hHa.continuousAt hHs ?_ ?_ ?_ hbij
    · refine analyticAt_const.mul ((analyticAt_const.mul hHa).cpow analyticAt_const ?_)
      show (H s)⁻¹ * H s ∈ Complex.slitPlane
      rw [inv_mul_cancel₀ hHs]
      exact Complex.one_mem_slitPlane
    · intro h
      rw [inv_mul_cancel₀ hHs, Complex.one_cpow, mul_one] at h
      apply hHs
      rw [← hroot (H s), h, zero_pow hm]
    · intro _ τ
      rw [mul_pow, hroot, hroot, mul_inv_cancel_left₀ hHs]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
