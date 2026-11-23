import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchFillDimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology MeasureTheory

noncomputable section

namespace BranchFillDimension

theorem hausdorffMeasure_pos_of_isOpen {d : ℕ} {V : Set (Fin d → ℂ)} (hV : IsOpen V)
    (hne : V.Nonempty) : 0 < μH[((2 * d : ℕ) : ℝ)] V := by
  have hr : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [← hr]
  exact hV.measure_pos _ hne

theorem not_open_subset_image {k d : ℕ} (hkd : k < d) {U : Set (Fin k → ℂ)} (hU : IsOpen U)
    {F : (Fin k → ℂ) → Fin d → ℂ} (hF : DifferentiableOn ℂ F U) {V : Set (Fin d → ℂ)}
    (hV : IsOpen V) (hne : V.Nonempty) : ¬ V ⊆ F '' U := by
  intro hsub
  let T : (Fin d → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE hkd.le i)
  have hT : ∀ u i, T u i = u (Fin.castLE hkd.le i) := fun _ _ => rfl
  have hU' : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
  have hg : DifferentiableOn ℂ (F ∘ T) (T ⁻¹' U) := hF.comp T.differentiableOn (fun _ hu => hu)
  have hcrit : T ⁻¹' U ⊆ {s | s ∈ T ⁻¹' U ∧ ¬ Function.Injective (fderiv ℂ (F ∘ T) s)} := by
    intro u hu
    refine ⟨hu, fun hinj => ?_⟩
    have hTe : T (Pi.single ⟨k, hkd⟩ 1) = 0 := by
      funext i
      have hi : Fin.castLE hkd.le i ≠ ⟨k, hkd⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hT, hi]
    have hfd : fderiv ℂ (F ∘ T) u = (fderiv ℂ F (T u)).comp T := by
      rw [fderiv_comp u ((hF (T u) hu).differentiableAt (hU.mem_nhds hu)) T.differentiableAt,
        T.fderiv]
    have h0 : (Pi.single ⟨k, hkd⟩ (1 : ℂ) : Fin d → ℂ) = 0 :=
      hinj (by rw [hfd]; simp [hTe])
    have := congrFun h0 ⟨k, hkd⟩
    simp at this
  have hnull := CriticalImageNull.proof d d (T ⁻¹' U) (F ∘ T) hU' hg
  have hsub' : V ⊆ (F ∘ T) '' {s | s ∈ T ⁻¹' U ∧ ¬ Function.Injective (fderiv ℂ (F ∘ T) s)} := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hsub hy
    have hext : T (fun j => if hj : j.val < k then t ⟨j.val, hj⟩ else 0) = t := by
      funext i
      simp [hT]
    refine ⟨_, hcrit (show _ ∈ T ⁻¹' U from hext ▸ ht), ?_⟩
    simp only [Function.comp_apply, hext]
  exact (hausdorffMeasure_pos_of_isOpen hV hne).ne' (measure_mono_null hsub' hnull)

theorem of_fin (hHF : HolomorphicFibreInfinite.Statement) (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (h : MvPolynomial (Fin n) ℂ) (w : Fin n → ℂ) (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → Fin n → ℂ)
    (B : Set (Fin n → ℂ)) (hJ : J.IsPrime) (hh : h ∉ J) (hw : w ∈ zeroLocus J)
    (hφd : DifferentiableOn ℂ φ (Metric.ball 0 r)) (hφi : Set.InjOn φ (Metric.ball 0 r))
    (hφm : Set.MapsTo φ (Metric.ball 0 r) (zeroLocus J)) (hB : B ∈ 𝓝 w)
    (hcov : (zeroLocus J ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
    induction x using WithBot.recBotCoe with
    | bot => simp at h0
    | coe m =>
      induction m using ENat.recTopCoe with
      | top =>
        exfalso
        have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
        exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
      | coe m => exact ⟨m, rfl⟩
  obtain ⟨A, hA⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.proof n d J hd
  let π : (Fin n → ℂ) → Fin d → ℂ := fun z => A.mulVec z
  have hπe : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = π := by
    funext z i
    simp [π, GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
  have hπd : Differentiable ℂ π := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  obtain ⟨z0, ⟨hz0, hhz0⟩, hz0B⟩ : ∃ z0, (z0 ∈ zeroLocus J ∧ eval z0 h ≠ 0) ∧ z0 ∈ interior B := by
    have hfreq : ∃ᶠ y in 𝓝 w, y ∈ zeroLocus J ∧ eval y h ≠ 0 := by
      intro hev
      exact hh (VanishNearPoint.proof FiniteMapOpen.proof n J h w hJ hw
        (hev.mono fun y hy hyZ => by by_contra hne; exact hy ⟨hyZ, hne⟩))
    exact (hfreq.and_eventually (interior_mem_nhds.2 hB)).exists
  have hUo : IsOpen (interior B ∩ {z | eval z h ≠ 0}) :=
    isOpen_interior.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)
  have hnb := FiniteMapOpen.proof n d J (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hJ hA.injective
    hA.finite z0 hz0 _ (hUo.mem_nhds ⟨hz0B, hhz0⟩)
  rw [hπe] at hnb
  have hsub : π '' (zeroLocus J ∩ (interior B ∩ {z | eval z h ≠ 0})) ⊆ (π ∘ φ) '' Metric.ball 0 r := by
    rintro _ ⟨z, ⟨hzZ, hzB, hzh⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hcov ⟨⟨hzZ, interior_subset hzB⟩, hzh⟩
    exact ⟨t, ht, rfl⟩
  have hΔ : (Metric.ball (0 : Fin k → ℂ) r).Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov ⟨⟨hz0, interior_subset hz0B⟩, hhz0⟩
    exact ⟨t, ht⟩
  have hle : k ≤ d := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy⟩ := hHF k d _ (π ∘ φ) hlt Metric.isOpen_ball hΔ (hπd.comp_differentiableOn hφd)
    have hfin := (GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof n d J A hJ hd hA y).2.1
    apply hy
    have hmaps : φ '' {t | t ∈ Metric.ball 0 r ∧ (π ∘ φ) t = y} ⊆
        GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y := by
      rintro _ ⟨t, ⟨ht, hty⟩, rfl⟩
      exact ⟨hφm ht, hty⟩
    exact Set.Finite.of_finite_image (hfin.subset hmaps) (hφi.mono fun t ht => ht.1)
  have hge : d ≤ k := by
    by_contra hlt
    push Not at hlt
    exact not_open_subset_image hlt Metric.isOpen_ball (hπd.comp_differentiableOn hφd) isOpen_interior
      ⟨_, mem_interior_iff_mem_nhds.2 hnb⟩ (interior_subset.trans hsub)
  rw [hd, le_antisymm hge hle]

end BranchFillDimension

theorem BranchFillDimension.proof (hHF : HolomorphicFibreInfinite.Statement) :
    BranchFillDimension.Statement := by
  intro σ _ I h w k r φ B hI hh hw hφd hφi hφm hB hcov
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let ψ : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ := (renameEquiv ℂ e).toRingEquiv
  have hψ : ∀ q, ψ q = rename e q := fun _ => rfl
  have hψs : ∀ q, ψ.symm q = rename e.symm q := fun _ => rfl
  let J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap ψ.symm
  have hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ q, q ∈ J ↔ ψ.symm q ∈ I := fun _ => Iff.rfl
  let L : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e.symm i)
  let M : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ) :=
    ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (e s)
  have hLM : ∀ x, L (M x) = x := fun x => funext fun i => by simp [L, M]
  have hML : ∀ z, M (L z) = z := fun z => funext fun s => by simp [L, M]
  have heval : ∀ z q, eval (L z) (ψ q) = eval z q := by
    intro z q
    have hc : L z ∘ e = z := funext fun s => by simp [L]
    rw [hψ, eval_rename, hc]
  have hZ : ∀ z, L z ∈ zeroLocus J ↔ z ∈ zeroSetIn I := by
    intro z
    constructor
    · intro hz q hq
      rw [← heval]
      exact hz _ (by rw [hmemJ, RingEquiv.symm_apply_apply]; exact hq)
    · intro hz q hq
      rw [← ψ.apply_symm_apply q, heval]
      exact hz _ ((hmemJ q).1 hq)
  have hdim : ringKrullDim (MvPolynomial σ ℂ ⧸ I) = ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) ℂ ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J ψ (Ideal.comap_symm (I := I) ψ))
  rw [hdim]
  refine BranchFillDimension.of_fin hHF _ J (ψ h) (L w) k r (L ∘ φ) (M ⁻¹' B) hJ ?_ ((hZ w).2 hw)
    (L.differentiable.comp_differentiableOn hφd) ?_ ?_ ?_ ?_
  · rw [hmemJ, RingEquiv.symm_apply_apply]
    exact hh
  · intro t ht t' ht' htt
    exact hφi ht ht' (by simpa [hML] using congrArg M htt)
  · intro t ht
    exact (hZ _).2 (hφm ht)
  · exact M.continuous.continuousAt.preimage_mem_nhds (by rwa [hML])
  · rintro x ⟨⟨hxZ, hxB⟩, hxh⟩
    rw [← hLM x] at hxZ hxh
    obtain ⟨t, ht, hteq⟩ := hcov ⟨⟨(hZ _).1 hxZ, hxB⟩, fun h0 => hxh (by simpa [heval] using h0)⟩
    exact ⟨t, ht, by simp [hteq, hLM]⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
