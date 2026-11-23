import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc.Swap

theorem norm_eq_of_sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  apply le_antisymm
  · exact h1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.mp h2 with h3 | h3
    · exact absurd h3 (not_le.mpr h)
    · exact h3

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta x = eta y := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have := norm_eq_of_sub_lt hy
  unfold eta
  rw [this]

theorem continuous_eta_det {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    Continuous (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hc : Continuous (fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  exact ContinuousAt.comp (f := fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det)
    (continuousAt_const.congr (eta_eventually hd)) hc.continuousAt

theorem continuous_psi {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine ContinuousAt.congr (f := fun _ => ψ x) continuousAt_const ?_
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hy.le, mul_one]

theorem continuous_act {F : Type} [NontriviallyNormedField F] (r : ℕ) :
    Continuous (fun z : GL (Fin r) F × Gl r F => act z.1 z.2) := by
  unfold act
  have h1 : Continuous (fun z : GL (Fin r) F × Gl r F => ((z.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun z : GL (Fin r) F × Gl r F =>
      (((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_coe_inv.comp continuous_fst
  exact ((h1.matrix_mul continuous_snd.fst).matrix_mul h2).prodMk
    ((h1.matrix_mulVec continuous_snd.snd.fst).prodMk
      ((continuous_snd.snd.snd.fst.matrix_vecMul h2).prodMk continuous_snd.snd.snd.snd))

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] (A : Et F E)

theorem K_inst {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) [SecondCountableTopology F] :
    T2Space A.K ∧ SecondCountableTopology A.K := by
  have hc : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have hc' : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  let e : A.K ≃ₜ (Fin r → F) :=
    { toEquiv := (bas A hG).equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨e.isEmbedding.t2Space, e.isEmbedding.secondCountableTopology⟩

theorem continuous_pt {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F) :
    Continuous (fun q : A.K × A.K => pt A hG lam q.1 q.2) := by
  unfold pt
  have he : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.prodMk ((he.comp continuous_fst).prodMk
    ((continuous_pi fun i => htr.comp (continuous_const.mul continuous_snd)).prodMk continuous_const))

end GlobalTheory.JR.LinDesc.Swap

namespace GlobalTheory.JR.LinDesc.Swap

theorem swap_triple {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    [SigmaFinite ν] (k : X → Y → Y → ℂ) (hk : Continuous (fun z : (Y × Y) × X => k z.2 z.1.1 z.1.2))
    (S : Set X) (B C : Set Y) (hS : IsCompact S) (hB : IsCompact B) (hC : IsCompact C)
    (hsupp : ∀ g b c, k g b c ≠ 0 → g ∈ S ∧ b ∈ B ∧ c ∈ C) :
    ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ b, ∫ c, ∫ g, k g b c ∂μ ∂ν ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
  set Φ : (Y × Y) × X → ℂ := fun z => k z.2 z.1.1 z.1.2 with hΦdef
  have hΦc : HasCompactSupport Φ := by
    refine HasCompactSupport.intro ((hB.prod hC).prod hS) fun z hz => ?_
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hsupp _ _ _ h
    exact hz ⟨⟨h2, h3⟩, h1⟩
  have hΦ : Integrable Φ ((ν.prod ν).prod (μ.restrict S)) := hk.integrable_of_hasCompactSupport hΦc
  have hL : ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    have : ∀ b c, k g b c = 0 := fun b c => by
      by_contra h; exact hg (hsupp _ _ _ h).1
    simp [this]
  have hR : ∀ b c, ∫ g, k g b c ∂μ = ∫ g in S, k g b c ∂μ := fun b c => by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra h; exact hg (hsupp _ _ _ h).1
  simp_rw [hR]
  rw [hL]
  calc ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ
      = ∫ g, ∫ q, Φ (q, g) ∂(ν.prod ν) ∂(μ.restrict S) := by
        refine integral_congr_ae ?_
        filter_upwards [hΦ.prod_left_ae] with g hg
        exact (integral_prod (fun q => Φ (q, g)) hg).symm
    _ = ∫ q, ∫ g, Φ (q, g) ∂(μ.restrict S) ∂(ν.prod ν) :=
        (integral_integral_swap (f := fun q g => Φ (q, g)) hΦ).symm
    _ = ∫ b, ∫ c, ∫ g in S, k g b c ∂μ ∂ν ∂ν := integral_prod _ hΦ.integral_prod_left

end GlobalTheory.JR.LinDesc.Swap

namespace GlobalTheory.JR.LinDesc.Swap

theorem desc_fourG_eq_fourK_desc : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  intro F E _ _ _ _ _ A r τ p hG lam M ψ hψ μK hμK α f' hf' hα hαc hyp x
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨hT2, hSC⟩ := K_inst A hG
  haveI := hT2
  haveI := hSC
  haveI := hμK.1
  set k : GL (Fin r) F → A.K → A.K → ℂ := fun g b' c' =>
    f' (act g (pt A hG lam b' c')) * A.psiK ψ (x.1 * c' + b' * x.2) *
      (eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ)) with hk
  have hL : desc A M hG lam α (fourG M ψ f') x = ∫ g, ∫ b', ∫ c', k g b' c' ∂μK ∂μK ∂M.μG := by
    unfold desc
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    rw [hyp g x.1 x.2]
    unfold Et.fourK
    rw [mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    simp only
    rw [← integral_mul_const]
  have hR : A.fourK μK ψ (desc A M hG lam α f') x = ∫ b', ∫ c', ∫ g, k g b' c' ∂M.μG ∂μK ∂μK := by
    unfold Et.fourK desc
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hk]; ring
  rw [hL, hR]
  have hbij := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let ρl : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i : Fin r => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  let ρe : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρl (by exact hbij)
  have hρs : Continuous ρe.symm := IsModuleTopology.continuous_of_linearMap ρe.symm.toLinearMap
  have hes : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hST : IsCompact (tsupport α ×ˢ tsupport f') := hαc.prod hf'.2
  refine swap_triple M.μG μK k ?_ (tsupport α)
    ((bas A hG).equivFun.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      ((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ z.2.2.1) '' (tsupport α ×ˢ tsupport f')))
    (ρe.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      z.2.2.2.1 ᵥ* (z.1 : Matrix (Fin r) (Fin r) F)) '' (tsupport α ×ˢ tsupport f')))
    hαc ?_ ?_ ?_
  · have h1 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => f' (act z.2 (pt A hG lam z.1.1 z.1.2))) :=
      hf'.1.continuous.comp ((continuous_act r).comp
        (continuous_snd.prodMk ((continuous_pt A hG lam).comp continuous_fst)))
    have h2 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => A.psiK ψ (x.1 * z.1.2 + z.1.1 * x.2)) :=
      (continuous_psi ψ hψ).comp (htr.comp
        ((continuous_const.mul continuous_fst.snd).add (continuous_fst.fst.mul continuous_const)))
    have h3 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => eta ((z.2 : Matrix (Fin r) (Fin r) F).det)) :=
      (continuous_eta_det r).comp continuous_snd
    have h4 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => ((α z.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hα.continuous.comp continuous_snd)
    exact (h1.mul h2).mul (h3.mul h4)
  · exact (hST.image ((Units.continuous_coe_inv.comp continuous_fst).matrix_mulVec
      continuous_snd.snd.fst)).image hes
  · exact (hST.image (continuous_snd.snd.snd.fst.matrix_vecMul
      (Units.continuous_val.comp continuous_fst))).image hρs
  · intro g b c hne
    have hf0 : f' (act g (pt A hG lam b c)) ≠ 0 := fun h => hne (by simp only [hk, h, zero_mul])
    have hα0 : α g ≠ 0 := fun h => hne (by simp only [hk, h, Complex.ofReal_zero, mul_zero])
    have hgS : g ∈ tsupport α := subset_tsupport _ hα0
    have hYT : act g (pt A hG lam b c) ∈ tsupport f' := subset_tsupport _ hf0
    have hinv : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨hgS, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩⟩
    · simp only [act, pt, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
    · have hρc : ρe c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := rfl
      simp only [act, pt, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
      rw [← hρc, LinearEquiv.symm_apply_apply]

end GlobalTheory.JR.LinDesc.Swap
