import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv

noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants Matrix GlobalTheory.SmVec GlobalTheory.SmVec.WordCont MeasureTheory Filter Asymptotics
open GlobalTheory.UnitarySmVec (pr pr_zero pr_succ pr_conj)
open scoped ContDiff InnerProductSpace Topology

namespace GlobalTheory.SmoothAverage

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem pr_mem' (hG : IsUnit G) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieG G)
    (t : Fin k → ℝ) : pr Xs t ∈ UH G := expProd_mem_UH hG hX t

theorem continuous_pr (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i, Xs i ∈ lieG G) (u : H) : Continuous fun t => π (pr Xs t) u :=
  (hπ.2.2 u).comp_continuous (GlobalTheory.GardingVec.contDiff_expProd Xs).continuous (pr_mem' hG hX)

theorem pr_add (hG : IsUnit G) : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ lieG G) →
    ∃ Y : (Fin k → ℝ) → Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, ContDiff ℝ ∞ fun t => Y t i) ∧
      (∀ t i, Y t i ∈ lieG G) ∧ ∀ t h, pr Xs (t + h) = pr Xs t * pr (Y t) h
  | 0, Xs, _ => ⟨fun _ => Xs, fun i => i.elim0, fun _ i => i.elim0, fun t h => by simp [pr_zero]⟩
  | k + 1, Xs, hX => by
    obtain ⟨Y, h1, h2, h3⟩ := pr_add hG (Fin.init Xs) fun i => hX _
    set X := Xs (Fin.last k) with hXd
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    have hm : ∀ s : ℝ, NormedSpace.exp (s • X) ∈ UH G := exp_mem_UH hG (hX _)
    refine ⟨fun t => Fin.snoc (fun i => (NormedSpace.exp (t (Fin.last k) • X))⁻¹ * Y (Fin.init t) i *
      NormedSpace.exp (t (Fin.last k) • X)) X, fun i => ?_, fun t i => ?_, fun t h => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using contDiff_const
      · simp only [Fin.snoc_castSucc, ← Matrix.exp_neg]
        have a1 : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => t (Fin.last k) • X :=
          (contDiff_apply ℝ ℝ (Fin.last k)).smul contDiff_const
        have a2 : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => (Fin.init t : Fin k → ℝ) :=
          contDiff_pi.2 fun j => contDiff_apply ℝ ℝ _
        exact ((hexp.comp a1.neg).mul ((h1 j).comp a2)).mul (hexp.comp a1)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hX _
      · simpa using conj_mem_lieG hG (hm _) (h2 _ j)
    · have hd := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_mem_UH hG (hm (t (Fin.last k))))
      have e : Fin.init (t + h) = Fin.init t + Fin.init h := rfl
      rw [pr_succ, pr_succ, pr_succ, e, h3, Fin.init_snoc]
      simp only [Fin.snoc_last]
      rw [← hXd, Pi.add_apply, add_smul,
        Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc _ (pr _ _), pr_conj hd, ← Matrix.mul_assoc]

theorem hasFDerivAt_pr_zero (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {v : H} :
    ∀ {k : ℕ} (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Ys i ∈ lieG G) → ∀ d : Fin k → H,
    (∀ i, HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • Ys i)) v) (d i) 0) →
    HasFDerivAt (fun h => π (pr Ys h) v)
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (d i)) 0
  | 0, Ys, _, d, _ => by simpa [pr_zero] using hasFDerivAt_const _ _
  | k + 1, Ys, hY, d, hd => by
    have ih := hasFDerivAt_pr_zero hG hπ (Fin.init Ys) (fun i => hY _) (Fin.init d) fun i => hd _
    let I : (Fin (k + 1) → ℝ) →L[ℝ] (Fin k → ℝ) :=
      ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) j.castSucc
    let L : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) (Fin.last k)
    have hI : ∀ h, I h = Fin.init h := fun _ => rfl
    have hL : ∀ h, L h = h (Fin.last k) := fun _ => rfl
    have hY' : ∀ i, Fin.init Ys i ∈ lieG G := fun i => hY _
    set X := Ys (Fin.last k)
    set d₀ := d (Fin.last k)
    have b1 := HasFDerivAt.comp (0 : Fin (k + 1) → ℝ) (by rw [map_zero]; exact ih) I.hasFDerivAt
    have c1 : (fun s : ℝ => π (NormedSpace.exp (s • X)) v - v - s • d₀) =o[𝓝 0] fun s => s := by
      have := hasDerivAt_iff_isLittleO.1 (hd (Fin.last k))
      simpa [rep_one hπ] using this
    have tL : Tendsto L (𝓝 0) (𝓝 0) := L.continuous.tendsto' _ _ (map_zero L)
    have c2 : (fun h => π (pr (Fin.init Ys) (I h)) (π (NormedSpace.exp (L h • X)) v - v - L h • d₀)) =o[𝓝 0]
        fun h => h := by
      refine IsLittleO.of_norm_left ?_
      simp only [hπ.2.1 _ (pr_mem' hG hY' _)]
      exact ((c1.comp_tendsto tL).trans_isBigO (L.isBigO_id _)).norm_left
    have c3 : (fun h => L h • (π (pr (Fin.init Ys) (I h)) d₀ - d₀)) =o[𝓝 0] fun h => h := by
      have t1 : Tendsto (fun h => π (pr (Fin.init Ys) (I h)) d₀ - d₀) (𝓝 0) (𝓝 0) :=
        (((continuous_pr hG hπ hY' d₀).comp I.continuous).sub continuous_const).tendsto' _ _ (by
          simp [pr, rep_one hπ, d₀])
      have := (L.isBigO_id (𝓝 0)).norm_right.smul_isLittleO ((isLittleO_one_iff ℝ).2 t1)
      exact IsLittleO.of_norm_right (by simpa using this)
    have b2 : HasFDerivAt (fun h => π (pr Ys h) v - π (pr (Fin.init Ys) (I h)) v) (L.smulRight d₀) 0 := by
      rw [hasFDerivAt_iff_isLittleO]
      simp only [sub_zero]
      refine (c2.add c3).congr_left fun h => ?_
      rw [pr_succ, rep_mul hπ (pr_mem' hG hY' _) (exp_mem_UH hG (hY _) _)]
      have z1 : pr Ys 0 = 1 := by simp [pr]
      have z2 : pr (Fin.init Ys) (I 0) = 1 := by simp [pr]
      rw [z1, z2]
      simp only [map_sub, hI, hL, ContinuousLinearMap.map_smul_of_tower, smul_sub,
        ContinuousLinearMap.smulRight_apply]
      abel
    have b3 := b1.add b2
    refine (b3.congr_of_eventuallyEq (Eventually.of_forall fun h => by simp)).congr_fderiv ?_
    ext h
    simp [Fin.sum_univ_castSucc, I, L, Fin.init, d₀]

theorem mem_smSub_of_closed (hG : IsUnit G) (hπ : IsURepOn (UH G) π) (N : Set H)
    (hN : ∀ v ∈ N, ∃ D : lieSub G →ₗ[ℝ] H, ∀ X : lieSub G, D X ∈ N ∧
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X.1)) v) (D X) 0) : ∀ v ∈ N, v ∈ smSub G π := by
  let b := Module.finBasis ℝ (lieSub G)
  choose c hc using fun j => LinearMap.exists_extend (b.coord j)
  intro v hv k Xs hX
  obtain ⟨Y, h1, h2, h3⟩ := pr_add hG Xs hX
  have ind : ∀ m : ℕ, ∀ v ∈ N, ContDiff ℝ m fun t => π (pr Xs t) v := by
    intro m
    induction m with
    | zero => intro v _; exact contDiff_zero.2 (continuous_pr hG hπ hX v)
    | succ m ih =>
      intro v hv
      obtain ⟨D, hD⟩ := hN v hv
      have hF : ∀ t, HasFDerivAt (fun t => π (pr Xs t) v) (((π (pr Xs t)).restrictScalars ℝ).comp
          (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (D ⟨Y t i, h2 t i⟩))) t := by
        intro t
        have a1 := hasFDerivAt_pr_zero hG hπ (Y t) (h2 t) _ fun i => (hD ⟨Y t i, h2 t i⟩).2
        rw [← sub_self t] at a1
        have a2 := ((π (pr Xs t)).restrictScalars ℝ).hasFDerivAt.comp t
          (HasFDerivAt.comp (f := fun s => s - t) t a1 ((hasFDerivAt_id t).sub_const t))
        refine (a2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_fderiv (by ext; simp)
        show _ = π _ (π _ v)
        rw [← rep_mul hπ (pr_mem' hG hX _) (pr_mem' hG (h2 t) _), ← h3, add_sub_cancel]
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun t => (hF t).differentiableAt, by simp, fun z => ?_⟩
      have e : ∀ t i, D ⟨Y t i, h2 t i⟩ = ∑ j, c j (Y t i) • D (b j) := fun t i => by
        conv_lhs => rw [← b.sum_repr ⟨Y t i, h2 t i⟩, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ← b.coord_apply, ← hc j]
        rfl
      simp only [(hF _).fderiv, e, ContinuousLinearMap.comp_apply, _root_.sum_apply,
        ContinuousLinearMap.smulRight_apply, map_sum, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.map_smul_of_tower]
      refine ContDiff.sum fun i _ => ContDiff.const_smul _ (ContDiff.sum fun j _ =>
        ContDiff.smul (f := fun t => c j (Y t i)) ?_ (ih _ (hD _).1))
      exact contDiff_infty.1 (((c j).toContinuousLinearMap.contDiff).comp (h1 i)) m
  exact contDiff_infty.2 fun m => ind m v hv

theorem hasDerivAt_orbit (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {u : H} (hu : u ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • X)) u) (π (NormedSpace.exp (t • X)) (dRep π X u)) t := by
  have a1 := ((π (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_dRep hu hX)
  rw [← sub_self t] at a1
  refine (a1.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show _ = π _ (π _ u)
  rw [← rep_mul hπ (exp_mem_UH hG hX _) (exp_mem_UH hG hX _),
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul, add_sub_cancel]

section Integral

variable [CompleteSpace H] {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  (μ : Measure K) [IsFiniteMeasureOnCompacts μ]

def SmoothFamily (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (F : K → H) : Prop :=
  (∀ k, F k ∈ smSub G π) ∧ ∀ l, (∀ X ∈ l, X ∈ lieG G) → Continuous fun k => word π l (F k)

theorem integrable_of_continuous {E : Type} [NormedAddCommGroup E] {F : K → E} (hF : Continuous F) :
    Integrable F μ := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

omit [CompleteSpace H] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] in
theorem SmoothFamily.word (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {F : K → H} (hF : SmoothFamily G π F)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    SmoothFamily G π fun k => word π l (F k) :=
  ⟨fun k => word_mem hG hπ hl (hF.1 k), fun l' hl' => by
    simp only [← word_append]
    exact hF.2 _ fun X hX => (List.mem_append.1 hX).elim (hl' X) (hl X)⟩

theorem SmoothFamily.hasDerivAt (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {F : K → H} (hF : SmoothFamily G π F)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (∫ k, F k ∂μ)) (∫ k, dRep π X (F k) ∂μ) 0 := by
  have c0 : Continuous F := hF.2 [] (by simp)
  have c1 : Continuous fun k => dRep π X (F k) := hF.2 [X] (by simpa using hX)
  have i0 := integrable_of_continuous μ c0
  have i1 := integrable_of_continuous μ c1
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) k => π (NormedSpace.exp (t • X)) (F k))
    (F' := fun (t : ℝ) k => π (NormedSpace.exp (t • X)) (dRep π X (F k))) (bound := fun k => ‖dRep π X (F k)‖)
    univ_mem (Eventually.of_forall fun t => ((π _).integrable_comp i0).1) ((π _).integrable_comp i0)
    ((π _).integrable_comp i1).1
    (Eventually.of_forall fun k t _ => (hπ.2.1 _ (exp_mem_UH hG hX t) _).le) i1.norm
    (Eventually.of_forall fun k t _ => hasDerivAt_orbit hG hπ (hF.1 k) hX t)).2
  simpa only [ContinuousLinearMap.integral_comp_comm _ i0, zero_smul, NormedSpace.exp_zero, rep_one hπ] using this

theorem SmoothFamily.word_integral (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {F : K → H} (hF : SmoothFamily G π F)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    GlobalTheory.SmVec.word π l (∫ k, F k ∂μ) = ∫ k, GlobalTheory.SmVec.word π l (F k) ∂μ := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    rw [word_cons, ih hl']
    exact ((hF.word hG hπ hl').hasDerivAt μ hG hπ (hl X (by simp))).deriv

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P : Matrix (Fin n) (Fin n) ℂ}

theorem SmoothFamily.integral_mem (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {F : K → H} (hF : SmoothFamily G (trRep σ P) F) : ∫ k, F k ∂μ ∈ smSub G (trRep σ P) := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  refine mem_smSub_of_closed hG hπ {v | ∃ F : K → H, SmoothFamily G (trRep σ P) F ∧ ∫ k, F k ∂μ = v} ?_ _
    ⟨F, hF, rfl⟩
  rintro _ ⟨F, hF, rfl⟩
  have hw : ∀ X : lieSub G, SmoothFamily G (trRep σ P) fun k => dRep (trRep σ P) X (F k) := fun X =>
    hF.word hG hπ (l := [X.1]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact X.2
  have hi : ∀ X : lieSub G, Integrable (fun k => dRep (trRep σ P) X (F k)) μ := fun X =>
    integrable_of_continuous μ ((hw X).2 [] (by simp))
  have hlin := fun k => GlobalTheory.SmVecLinear.dRep_linear n ε H σ P G hP h hσ _ (hF.1 k)
  refine ⟨{ toFun := fun X => ∫ k, dRep (trRep σ P) X (F k) ∂μ
            map_add' := fun X Y => ?_
            map_smul' := fun a X => ?_ }, fun X => ⟨⟨_, hw X, rfl⟩, hF.hasDerivAt μ hG hπ X.2⟩⟩
  · rw [← integral_add (hi X) (hi Y)]
    simp only [Submodule.coe_add, fun k => (hlin k).1 _ X.2 _ Y.2]
  · rw [RingHom.id_apply, ← integral_smul]
    simp only [Submodule.coe_smul, fun k => (hlin k).2 a _ X.2, Complex.coe_smul]

theorem SmoothFamily.form (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {F : K → H} (hF : SmoothFamily G (trRep σ P) F) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieG G) (trRep σ P) ℓ) :
    (Continuous fun k => ℓ (F k)) ∧ ℓ (∫ k, F k ∂μ) = ∫ k, ℓ (F k) ∂μ := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  obtain ⟨m, ls, a, hls, hrep⟩ := sobCont_repr n ε H σ P G hP h hσ ℓ hℓ
  have hc : ∀ i, Continuous fun k => ⟪a i, GlobalTheory.SmVec.word (trRep σ P) (ls i) (F k)⟫_ℂ := fun i =>
    continuous_const.inner (hF.2 _ (hls i))
  simp only [fun k => hrep _ (hF.1 k)]
  refine ⟨continuous_finsetSum _ fun i _ => hc i, ?_⟩
  rw [hrep _ (hF.integral_mem μ hP h hσ), integral_finsetSum _ fun i _ => integrable_of_continuous μ (hc i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF.word_integral μ hG hπ (hls i), integral_inner (integrable_of_continuous μ (hF.2 _ (hls i)))]

end Integral

theorem smoothFamily_orbit [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {e : Formalism.REAL.KG ε → ℂ} (he : Continuous e) {w : H} (hw : w ∈ smSub G (trRep σ P)) :
    SmoothFamily G (trRep σ P) fun k : Formalism.REAL.KG ε => e k • σ (Formalism.REAL.toMK k) w := by
  have hm : ∀ k : Formalism.REAL.KG ε, σ (Formalism.REAL.toMK k) w ∈ smSub G (trRep σ P) := fun k =>
    sigma_mem hP h hσ hw (k : Formalism.REAL.UJ ε).2
  refine ⟨fun k => Submodule.smul_mem _ _ (hm k), fun l hl => ?_⟩
  simp only [fun k => word_smul (gram_unit hP h) (isURepOn_trRep hP h hσ) hl (e k) (hm k)]
  exact he.smul ((continuous_word_translate n ε H σ P G hP h hσ l hl w hw).comp continuous_subtype_val)

end GlobalTheory.SmoothAverage

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.Chain.IoLift in

theorem GlobalTheory.SmoothAverage.kMean_smooth : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ), Continuous e → ∀ w ∈ M.sm τ, kMean M τ e w ∈ M.sm τ ∧ ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (Continuous fun k : Formalism.REAL.KG (M.ε τ) => ℓ (M.σ τ (Formalism.REAL.toMK k) w)) ∧ ℓ (kMean M τ e w) = ∫ k, e k * ℓ (M.σ τ (Formalism.REAL.toMK k) w) ∂(Formalism.REAL.muK (M.ε τ)) := by
  intro D V S M τ e he w hw
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ := (M.ds τ).2.2.1
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  rw [sm_eq] at hw ⊢
  have hF := GlobalTheory.SmoothAverage.smoothFamily_orbit hP h hσ he hw
  refine ⟨hF.integral_mem _ hP h hσ, fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · have h1 := GlobalTheory.SmoothAverage.smoothFamily_orbit hP h hσ (e := fun _ => 1) continuous_const hw
    simpa only [one_smul] using (h1.form (Formalism.REAL.muK (M.ε τ)) hP h hσ hℓ).1
  · simpa only [kMean, map_smul, smul_eq_mul] using (hF.form (Formalism.REAL.muK (M.ε τ)) hP h hσ hℓ).2

end
