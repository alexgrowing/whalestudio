import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormArchLeSupInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaFree

theorem schr_finset_sum {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) {ι : Type} (s : Finset ι) (φ : ι → (κ → R) → ℂ) :
    schr ψ w (∑ k ∈ s, φ k) = ∑ k ∈ s, schr ψ w (φ k) := by
  funext x
  simp only [schr, Finset.sum_apply, Finset.mul_sum]

theorem actAB_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E} (p : UA σ JX × UA σ JW) (a : AF F)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (a • u) = a • actAB (cA σ) p u := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem dH_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArch (M.co.e u) → dH B.ψ (M.co.e (actAB (cA σ) p u)) (om p Φ) = om p (dH B.ψ (M.co.e u) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ p u hu
  have hψ : IsStd B.ψ := hP.1
  have hS := IsUWeilPair.isUSplitting hP.2
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  have hAt : At (evI F) u := by
    intro a ha
    apply M.co.e.injective
    rw [map_smul, map_zero]
    exact Prod.ext (funext fun i => (hu i).1 a ha) (funext fun i => (hu i).2 a ha)
  obtain ⟨m, c, q, hq⟩ := Submodule.mem_span_set'.mp hΦ
  choose f g hg hfg using fun i => (q i).2
  set f' : Fin m → SInf F (Fin n × Fin d) := fun i => c i • f i with hf'
  have hΦe : Φ = ∑ i, pureA F (f' i) (g i) := by
    rw [← hq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfg i]
    funext x
    simp [f', pureA, mul_assoc]
  have hrho : ∀ (t : ℝ) (Ψ : (Fin n × Fin d → AF F) → ℂ),
      M.co.rho B.ψ (realAd F t • u) Ψ = schr B.ψ (realAd F t • M.co.e u) Ψ := by
    intro t Ψ
    rw [Darboux.rho, map_smul]

  have hdΦ : dH B.ψ (M.co.e u) Φ = ∑ i, pureA F (D u (f' i)) (g i) := by
    funext y
    have h : ∀ i, HasDerivAt (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y)
        (pureA F (D u (f' i)) (g i) y) 0 := by
      intro i
      have := (hD u hAt (f' i)).1 (g i) (hg i) (GlobalTheory.ExpAct.evalAt y) (GlobalTheory.ExpAct.evalAt_mem_adm F _ y)
      simpa only [GlobalTheory.ExpAct.evalAt, LinearMap.proj_apply, hrho] using this
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
    have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) Φ y) =
        fun t => ∑ i, schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y := by
      funext t
      rw [hΦe, schr_finset_sum, Finset.sum_apply]
    rw [dH, e, hs.deriv, Finset.sum_apply]
  funext x
  set l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.ExpAct.evalAt x ∘ₗ om p with hl
  have hladm : l ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm p _ (GlobalTheory.ExpAct.evalAt_mem_adm F _ x)
  have h : ∀ i, HasDerivAt (fun t : ℝ => l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))))
      (l (pureA F (D u (f' i)) (g i))) 0 := fun i => (hD u hAt (f' i)).1 (g i) (hg i) l hladm
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
  have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e (actAB (cA σ) p u)) (om p Φ) x) =
      fun t => ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) := by
    funext t
    have e1 : ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) = l (M.co.rho B.ψ (realAd F t • u) Φ) := by
      rw [← map_sum, hΦe, Darboux.rho, schr_finset_sum]
    rw [e1, hl, LinearMap.comp_apply, hS.impl p _ Φ hΦ, actAB_smul, Darboux.rho, map_smul]
    rfl
  rw [dH, e, hs.deriv, ← map_sum, hdΦ, hl, LinearMap.comp_apply]
  rfl

open scoped Classical in

theorem archUnit_act_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∃ C : ℝ, ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om _
  have evI_mul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 * b.1) = _
    exact map_mul _ _ _
  have evI_sub : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 - b.1) = _
    exact map_sub _ _ _
  have evI_one : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have evI_realAd : ∀ t : ℝ, evI F (realAd F t) = algebraMap ℝ _ t := fun t => by
    simp only [evI, realAd, LinearMap.inl_apply, RingEquiv.apply_symm_apply]
  obtain ⟨K5, hK5, h5⟩ := GlobalTheory.ThetaDecay.linMap_archBound F E n d (Fin n × Fin d) M.co.e.symm.toLinearMap
  obtain ⟨K3, hK3, h3⟩ := GlobalTheory.ThetaDecay.Coord.coord_bound F E
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.ThetaDecay.arch_bound_pair F E n d (Fin n × Fin d) M.co.e.toLinearMap
  refine ⟨K4 * (K3 * (n * d * K5)) + 1, fun p u hu => ?_⟩
  have hg : (1 : ℝ) ≤ ht p.1 := by
    have := one_le_heightGL F (p.1 : GL (Fin n) (AF F ⊗[F] E))
    exact_mod_cast this
  have hh : (1 : ℝ) ≤ ht p.2 := by
    have := one_le_heightGL F (p.2 : GL (Fin d) (AF F ⊗[F] E))
    exact_mod_cast this
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (ht p.1 : ℝ) * ht p.2 := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (K4 * (K3 * (n * d * K5)) + 1) * H := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    have : 0 < H := by rw [hH]; nlinarith
    positivity
  obtain ⟨x, hx⟩ : ∃ x, x = actAB (cA σ) p u := ⟨_, rfl⟩
  have s1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (u k l)‖ ≤ K5 * 1 := by
    have := h5 (M.co.e u) 1 zero_le_one (fun w i =>
      ⟨((GlobalTheory.ThetaDecay.norm_evI_sup F _).1 w).trans (hu.2 i).1, ((GlobalTheory.ThetaDecay.norm_evI_sup F _).1 w).trans (hu.2 i).2⟩)
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using this
  have s2 := GlobalTheory.WeilDirBound.norm_piInf_actAB_le_target F E σ n d X.J W.J p u (K5 * 1) (by positivity) s1
  rw [← hx, ← hH] at s2
  have s3 : ∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ K3 * (n * d * H * (K5 * 1)) :=
    fun w k l r => h3 (x k l) _ (by positivity) (fun w τ => s2 w τ k l) r w
  have s4 := h4 x _ (by positivity) s3
  have hbound : K4 * (K3 * (n * d * H * (K5 * 1))) ≤ c := by
    have e1 : K4 * (K3 * (n * d * H * (K5 * 1))) = K4 * (K3 * (n * d * K5)) * H := by ring
    rw [e1, hc]
    exact mul_le_mul_of_nonneg_right (by linarith) hH0
  have s5 : ∀ i, ‖evI F ((M.co.e x).1 i)‖ ≤ c ∧ ‖evI F ((M.co.e x).2 i)‖ ≤ c := fun i =>
    ⟨(GlobalTheory.ThetaDecay.norm_evI_sup F _).2 c hcpos.le (fun w => ((s4 w i).1).trans hbound),
     (GlobalTheory.ThetaDecay.norm_evI_sup F _).2 c hcpos.le (fun w => ((s4 w i).2).trans hbound)⟩
  have key : ∀ a : AF F, evI F a = 0 → a • M.co.e x = 0 := by
    intro a ha
    have h0 : a • M.co.e u = 0 := by
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · exact (hu.1 j).1 a ha
      · exact (hu.1 j).2 a ha
    have hu0 : a • u = 0 := by
      have := congrArg M.co.e.symm h0
      rwa [map_smul, LinearEquiv.symm_apply_apply, map_zero] at this
    rw [← map_smul, hx]
    have : a • actAB (cA σ) p u = actAB (cA σ) p (a • u) := by
      simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [this, hu0]
    simp [actAB]
  have harch : IsArch (M.co.e x) := fun i =>
    ⟨fun a ha => by simpa using congrArg (fun z => z.1 i) (key a ha),
     fun a ha => by simpa using congrArg (fun z => z.2 i) (key a ha)⟩
  have hone : ∀ z : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), IsArch z → realAd F 1 • z = z := by
    intro z hz
    have h1 : evI F (1 - realAd F 1) = 0 := by
      rw [evI_sub, evI_one, evI_realAd, map_one, sub_self]
    have : (1 - realAd F 1) • z = 0 :=
      Prod.ext (funext fun j => (hz j).1 _ h1) (funext fun j => (hz j).2 _ h1)
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  refine ⟨c, hcpos.le, by rw [hc, hH], realAd F c⁻¹ • M.co.e x, ⟨isArch_smul harch _, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).1 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).1 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).1 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).2 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).2 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).2 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · rw [smul_smul, realAd_mul, mul_inv_cancel₀ hcpos.ne', hone _ harch, hx]

theorem periodic_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ ∀ x a : Fin n × Fin d → AF F, (∀ i, evI F (a i) = 0 ∧ ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F) → om (g, h) Φ (x + (m : AF F) • a) = om (g, h) Φ x := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))
  refine ⟨m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((m₀ * N : ℕ) : ℝ) = m₀ * N := by push_cast; ring
    rw [this, mul_assoc (m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ := by
    clear hNle hC
    intro y hy
    set w' := M.co.e.symm (y, 0) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h2 h1
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  intro x a ha
  have hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a) := by
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · change fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0
      rw [map_mul]
      have h0 : fstA F (a i) = 0 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1
      rw [h0, mul_zero]
    · change ‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _
      rw [map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))
  have := congrFun (hfix _ hy) x
  simpa [schr] using this

theorem std_char_denom : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ D : ℕ, 0 < D ∧
    ∀ ξ : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) ξ * t) = 1) →
      ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _ ψ hψ
  obtain ⟨D, hD, h⟩ := GlobalTheory.exists_den_traceDual_ringOfIntegers (F := F)
  refine ⟨D, hD, fun ξ hξ => h ξ fun o => GlobalTheory.TraceIntStd.trace_int_of_isStd ψ hψ _ fun t ht0 ht1 => ?_⟩
  have e : algebraMap F (AF F) (ξ * o) * t = algebraMap F (AF F) ξ * (algebraMap F (AF F) o * t) := by
    rw [map_mul, mul_assoc]
  rw [e]
  refine hξ _ ?_ fun v => ?_
  · rw [show (algebraMap F (AF F) (o : F) * t).1 = (algebraMap F (AF F) (o : F)).1 * t.1 from rfl, ht0, mul_zero]
  · rw [map_mul, AlgHom.commutes, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ht1 v)
    refine Valued.toNormedField.norm_le_one_iff.2 ?_
    first
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact v.valuation_le_one o)
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact v.valuation_le_one o)
      | (exact (HeightOneSpectrum.coe_mem_adicCompletionIntegers v o))

theorem support_denom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (m : F) * ξ i = o := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨D, hD, hcond⟩ := std_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom M.co.e
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((D * m₀ * N : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)

  intro ξ hξ i
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (0, y) (om (g, h) Φ) = om (g, h) Φ := by
    clear hξ hcond hNle hC
    intro y hy
    set w' := M.co.e.symm (0, y) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h1 h2
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  obtain ⟨o, ho⟩ := hcond _ (fin_step B.ψ (m₀ * N) _ hfix ξ hξ i)
  exact ⟨o, by rw [← ho]; push_cast; ring⟩

section

variable {F : Type} [Field F] [NumberField F]

theorem evI_algebraMap_eq (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

open scoped Classical in
theorem sum_places_le : ∃ c : ℝ, ∀ ξ : F, ∑ w : InfinitePlace F, w ξ ≤ c * ‖evI F (algebraMap F (AF F) ξ)‖ := by
  refine ⟨Fintype.card (InfinitePlace F), fun ξ => ?_⟩
  rw [evI_algebraMap_eq]
  have h : ∀ w : InfinitePlace F, w ξ ≤ ‖mixedEmbedding F ξ‖ := by
    intro w
    rw [← mixedEmbedding.normAtPlace_apply w ξ]
    by_cases hw : w.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  calc ∑ w : InfinitePlace F, w ξ ≤ ∑ _w : InfinitePlace F, ‖mixedEmbedding F ξ‖ := Finset.sum_le_sum fun w _ => h w
    _ = _ := by simp

end

section

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordH_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.ThetaDecay.dH_mem_schA F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

end

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := by
  unfold ht
  exact heightGL_inv F g.1

theorem actAB_mul_inv {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (p : UA σ X.J × UA σ W.J)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ u) = u := by
  simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Matrix.transpose _), ← Matrix.transpose_mul]
  simp

end

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem word_transport {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} (hP : IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) {C : ℝ}
    (hC : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w)
    (p : UA σ X.J × UA σ W.J) :
    ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), (∀ w ∈ l, IsArchUnit w) →
      ∃ (c : ℝ) (l' : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))), 0 ≤ c ∧
        c ≤ (C * ((ht p.1 : ℝ) * ht p.2)) ^ l.length ∧ (∀ w ∈ l', IsArchUnit w) ∧ l'.length = l.length ∧
        wordH B.ψ l (om p Φ) = (c : ℂ) • om p (wordH B.ψ l' Φ) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, [], zero_le_one, by simp, by simp, rfl, by simp⟩
  | cons w l ih =>
    intro hl
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := ih (fun v hv => hl v (by simp [hv]))
    have hw : IsArchUnit w := hl w (by simp)
    obtain ⟨c', hc'0, hc'le, w', hw', he'⟩ := hC p⁻¹ (M.co.e.symm w) (by simpa using hw)
    have hF' : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) :=
      wordH_mem B.ψ hP.1 l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hT := dH_transport F E σ B n d X W M χX χW om hP _ hF' p (actAB (cA σ) p⁻¹ (M.co.e.symm w))
      (by rw [he']; exact isArch_smul hw'.1 _)
    rw [actAB_mul_inv, LinearEquiv.apply_symm_apply, he', dH_realAd_smul, map_smul] at hT
    refine ⟨c * c', w' :: l', mul_nonneg hc0 hc'0, ?_, ?_, by simp [hlen], ?_⟩
    · rw [List.length_cons, pow_succ]
      have : c' ≤ C * ((ht p.1 : ℝ) * ht p.2) := by simpa [ht_inv] using hc'le
      exact mul_le_mul hcle this hc'0 (hc0.trans hcle)
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hw'
      · exact hl' v hv
    · rw [wordH_cons, he, dH_smul, hT, wordH_cons, smul_smul, Complex.ofReal_mul]

end

section

theorem lintegral_sq_norm_le_of_smul {α : Type} {m : MeasurableSpace α} (μ : Measure α) (f g : α → ℂ) (c : ℝ) (hc0 : 0 ≤ c)
    (he : f = (c : ℂ) • g) (B₀ K : ℝ) (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B₀) (hcK : c ^ 2 ≤ K) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (K * max B₀ 0) := by
  have hcc : ‖(c : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc0, ENNReal.ofReal_pow hc0]
  subst he
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by rw [hcc]; exact ENNReal.ofReal_ne_top), hcc]
  calc ENNReal.ofReal (c ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ
      ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (max B₀ 0) :=
        by gcongr; exact hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (c ^ 2 * max B₀ 0) := (ENNReal.ofReal_mul (sq_nonneg c)).symm
    _ ≤ ENNReal.ofReal (K * max B₀ 0) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcK (le_max_right _ _))

theorem final_arith (P A S H m c₅ C₃ C₄ C₂ B₀ : ℝ) (N a k₄ ℓ : ℕ) (hP0 : 0 ≤ P) (hA0 : 0 ≤ A)
    (hA : A ≤ max c₅ 1 * (1 + S)) (hm0 : 0 ≤ m) (hm : m ≤ C₄ * H ^ k₄) (hH : 1 ≤ H)
    (key : P * (1 + S) ^ N ≤ C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0)) :
    P * A ^ N ≤ max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))) *
      H ^ (k₄ * a + 2 * ℓ) := by
  have hB₀' : (0 : ℝ) ≤ max B₀ 0 := le_max_right _ _
  have hC₂' : (1 : ℝ) ≤ max C₂ 1 := le_max_right _ _
  have hc₅' : (1 : ℝ) ≤ max c₅ 1 := le_max_right _ _
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hm' : m ≤ max C₄ 1 * H ^ k₄ :=
    hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))
  have hBw0 : 0 ≤ (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 := mul_nonneg (pow_nonneg (by positivity) _) hB₀'
  have h1B : 1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 ≤ (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ) := by
    have hH1 : 1 ≤ H ^ (2 * ℓ) := one_le_pow₀ hH
    rw [mul_pow]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ max C₂ 1 by linarith) (2 * ℓ)]
  calc P * A ^ N ≤ P * (max c₅ 1 * (1 + S)) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA N) hP0
    _ = max c₅ 1 ^ N * (P * (1 + S) ^ N) := by rw [mul_pow]; ring
    _ ≤ max c₅ 1 ^ N * (C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0)) :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (by linarith) _)
    _ ≤ max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 * H ^ k₄) ^ a * ((1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ))) := by
        gcongr
        · exact le_max_left _ _
    _ = _ := by
        rw [mul_pow, ← pow_mul, pow_add, mul_comm k₄ a]
        ring

theorem decay_at_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (ξ : Fin n × Fin d → F), ‖om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ N
  classical
  have hstd : IsStd B.ψ := hP.1
  have hU := hP.2.isUSplitting
  obtain ⟨μ, hμ, ℓ, a, C₃, h3⟩ := GlobalTheory.T.sobolev_uniform_bound_periodic F (Fin n × Fin d) N B.ψ hstd
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.ThetaSobolevBase.exists_l2_bound_heisenberg_word F (Fin n × Fin d) B.ψ hstd μ hμ Φ hΦ ℓ
  obtain ⟨C₂, h2⟩ := archUnit_act_bound F E σ B n d X W M χX χW om hP
  obtain ⟨C₄, k₄, h4⟩ := periodic_level F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨c₅, h5⟩ := sum_places_le (F := F)
  have hC₂ : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ max C₂ 1 * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧
        M.co.e (actAB (cA σ) p u) = realAd F c • w := fun p u hu => by
    obtain ⟨c, h0, hle, w, hw, he⟩ := h2 p u hu
    exact ⟨c, h0, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))), w, hw, he⟩
  refine ⟨max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))), k₄ * a + 2 * ℓ,
    fun g h ξ => ?_⟩
  have hH : (1 : ℝ) ≤ (ht g : ℝ) * ht h :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)
  have hCH : (1 : ℝ) ≤ max C₂ 1 * ((ht g : ℝ) * ht h) := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hH
  have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := hU.pres (g, h) Φ hΦ
  obtain ⟨m, hm1, hmle, hper⟩ := h4 g h
  have hwords : ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), l.length ≤ ℓ →
      (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH B.ψ l (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤
        ENNReal.ofReal ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) * max B₀ 0) := by
    intro l hl hu
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := word_transport hP hΦ hC₂ (g, h) l hu
    have hF : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) := wordH_mem B.ψ hstd l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hun := hU.unit μ hμ (g, h) _ hF
    have hc2 : c ^ 2 ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := by
      calc c ^ 2 ≤ ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ l.length) ^ 2 := pow_le_pow_left₀ hc0 hcle 2
        _ = (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * l.length) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := pow_le_pow_right₀ hCH (by omega)
    exact lintegral_sq_norm_le_of_smul μ _ _ c hc0 he B₀ _ (hun.trans_le (hB₀ l' (by omega) hl')) hc2
  have key := h3 (om (g, h) Φ) hΨ m hm1 hper _ (mul_nonneg (pow_nonneg (by linarith) _) (le_max_right _ _)) hwords
    (fun i => algebraMap F (AF F) (ξ i))
  have hS0 : 0 ≤ ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA0 : 0 ≤ 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => apply_nonneg w _)
  have hA : 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * (1 + ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖) := by
    have : ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => (h5 (ξ i)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ max c₅ 1 := le_max_right _ _
    nlinarith
  exact final_arith _ _ _ _ _ _ _ _ _ _ N a k₄ ℓ (norm_nonneg _) hA0 hA (Nat.cast_nonneg m) hmle hH key

end

theorem theta_moderateGrowth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨N, C₀, hC₀, hcount⟩ := GlobalTheory.RatPointSum.norm_thetaSum_le F (Fin n × Fin d)
  obtain ⟨C₂, k₂, hsupp⟩ := support_denom F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨C₃, k₃, hdec⟩ := decay_at_rational F E σ B n d X W M χX χW om hP Φ hΦ N
  refine ⟨C₀ * C₃ * C₂ ^ N, k₃ + k₂ * N, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hm⟩ := hsupp g h
  set x : ℝ := (ht g : ℝ) * ht h
  have hB : 0 ≤ C₃ * x ^ k₃ := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => w.1.nonneg _)) _)) (hdec g h 0)
  have key := hcount m (C₃ * x ^ k₃) (om (g, h) Φ) hm1 (hm) (hdec g h)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  calc ‖theta om Φ g h‖ = ‖GlobalTheory.WeilM.thetaSum F (om (g, h) Φ)‖ := rfl
    _ ≤ C₀ * (C₃ * x ^ k₃) * (m : ℝ) ^ N := key
    _ ≤ C₀ * (C₃ * x ^ k₃) * (C₂ * x ^ k₂) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmle N) (mul_nonneg hC₀ hB)
    _ = C₀ * C₃ * C₂ ^ N * x ^ (k₃ + k₂ * N) := by rw [mul_pow, pow_add, pow_mul]; ring

end GlobalTheory.ThetaFree

end
