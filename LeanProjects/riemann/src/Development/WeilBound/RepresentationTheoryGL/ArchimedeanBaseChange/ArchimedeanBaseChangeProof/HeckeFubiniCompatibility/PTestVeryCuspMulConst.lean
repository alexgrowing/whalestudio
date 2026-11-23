import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

instance pTest_t2Inf : T2Space (InfiniteAdeleRing E) :=
  inferInstanceAs (T2Space ((w : InfinitePlace E) → w.Completion))

open scoped RestrictedProduct in
instance pTest_t2Fin : T2Space (Af E) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))

instance pTest_t2Ad : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × Af E))

instance pTest_t2GA : T2Space (GA E n) := Units.isEmbedding_embedProduct.t2Space

theorem pTest_continuous_pInf : Continuous (pInf E : Ad E → Cinf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem pTest_continuous_gInf (v : InfinitePlace E) : Continuous (gInf (E := E) (n := n) v) :=
  Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp pTest_continuous_pInf))

theorem pTest_continuous_gFin : Continuous (gFin (E := E) (n := n)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem pTest_continuous_hFin : Continuous (hFin : H E a b → Hf E a b) :=
  (pTest_continuous_gFin.comp continuous_fst).prodMk (pTest_continuous_gFin.comp continuous_snd)

theorem pTest_continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem pTest_continuous_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) :=
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Cinf E) => 1 - matN n (sInf E) 1 + x.map (sInf E))

theorem pTest_continuous_of_inv {K : Type} [TopologicalSpace K] [Group K] [ContinuousMul K] (ψ : K → ℂ)
    (U : Subgroup K) (hU : IsOpen (U : Set K)) (h : ∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hm : (fun y => y * x⁻¹) ⁻¹' (U : Set K) ∈ 𝓝 x :=
    (hU.preimage (continuous_mul_const _)).mem_nhds (by simp [U.one_mem])
  exact continuousAt_const.congr (Filter.eventually_of_mem hm fun y hy => by
    simpa [mul_assoc] using (h _ hy x).symm)

def pTestY (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) where
  val := Matrix.of fun i j v => (y v).val i j
  inv := Matrix.of fun i j v => (y v)⁻¹.val i j
  val_inv := by
    ext i j v
    have h := congrFun (congrFun (y v).mul_inv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.one_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    rw [h]; split_ifs <;> rfl
  inv_val := by
    ext i j v
    have h := congrFun (congrFun (y v).inv_mul i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.one_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    rw [h]; split_ifs <;> rfl

theorem pTest_continuous_pTestY : Continuous (pTestY (E := E) (n := n)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => continuous_pi fun v =>
    (Units.continuous_val.comp (continuous_apply v)).matrix_elem i j, continuous_matrix fun i j => continuous_pi fun v =>
    ((Units.continuous_val.comp continuous_inv).comp (continuous_apply v)).matrix_elem i j⟩

theorem pTest_gInf_infGL (y : InfinitePlace E → G n) (v : InfinitePlace E) : gInf v (infGL E n (pTestY y)) = y v := by
  have h : ∀ x : Cinf E, cV v (sInf E x) = Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v x := fun x => by
    show (infEq E).symm (infEq E x) v = x v
    rw [RingEquiv.symm_apply_apply]
  show GeneralLinearGroup.map (cV v) (cornerGL n (sInf E) (pTestY y)) = y v
  rw [map_cornerGL_of_hom (sInf E) (cV v) _ h]
  ext i j; rfl

theorem pTest_gFin_infGL (y : GL (Fin n) (Cinf E)) : gFin (infGL E n y) = 1 := pFin_infGL y

theorem pTest_gInf_finGL (v : InfinitePlace E) (k : GL (Fin n) (Af E)) : gInf v (finGL E n k) = 1 :=
  map_cornerGL_of_zero (sFin E) (cV v) (fun x => by
    show (infEq E).symm 0 v = 0
    rw [map_zero]; rfl) k

theorem pTest_gFin_finGL (k : GL (Fin n) (Af E)) : gFin (finGL E n k) = k := pFin_finGL k

theorem pTest_decomp (x : GA E n) : infGL E n (pTestY fun v => gInf v x) * finGL E n (gFin x) = x := by
  have e : (pTestY fun v => gInf v x) = GeneralLinearGroup.map (pInf E) x := by ext i j v; rfl
  rw [e]; exact infGL_mul_finGL x

open Classical in
theorem pTest_embInf (v : InfinitePlace E) (d : G n) : embInf n v d = infGL E n (pTestY (Pi.mulSingle (M := fun _ : InfinitePlace E => G n) v d)) := by
  simp only [embInf, MonoidHom.comp_apply]
  congr 1

open Classical in
theorem pTest_gInf_embInf (v w : InfinitePlace E) (d : G n) : gInf w (embInf n v d) = Pi.mulSingle (M := fun _ : InfinitePlace E => G n) v d w := by
  rw [pTest_embInf, pTest_gInf_infGL]

theorem pTest_gFin_embInf (v : InfinitePlace E) (d : G n) : gFin (embInf n v d) = 1 := by
  classical
  rw [pTest_embInf, pTest_gFin_infGL]

theorem pTest_veryCusp_mul_const {f : G n → ℂ} (hf : VeryCusp f) (C : ℂ) : VeryCusp fun d => f d * C := by
  refine ⟨fun k d hk => by simp only [hf.1 k d hk], ?_⟩
  intro d W₁ W₂ h1 h2 h3 h4 u hu _ _ ν _
  rw [integral_mul_const, hf.2 d W₁ W₂ h1 h2 h3 h4 u hu ν, zero_mul]

theorem pTest_supp_fst {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {f : X × Y → ℂ}
    (hf : HasCompactSupport f) (y : Y) : HasCompactSupport fun x => f (x, y) :=
  HasCompactSupport.intro (hf.isCompact.image continuous_fst) fun x hx => by
    by_contra h; exact hx ⟨(x, y), subset_tsupport _ h, rfl⟩

theorem pTest_supp_snd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f : X × Y → ℂ}
    (hf : HasCompactSupport f) (x : X) : HasCompactSupport fun y => f (x, y) :=
  HasCompactSupport.intro (hf.isCompact.image continuous_snd) fun y hy => by
    by_contra h; exact hy ⟨(x, y), subset_tsupport _ h, rfl⟩

theorem pTest_slice (f : InfinitePlace E → G n → ℂ) (hf : ∀ v, VeryCusp (f v)) (χ : GL (Fin n) (Af E) → ℂ) (c : ℂ)
    (F : GA E n → ℂ) (hF : ∀ g, F g = c * (∏ v, f v (gInf v g)) * χ (gFin g)) (hFc : Continuous F)
    (hFs : HasCompactSupport F) (U : Subgroup (GL (Fin n) (Af E))) (hU : IsOpen (U : Set (GL (Fin n) (Af E))))
    (hχU : ∀ u ∈ U, ∀ k, χ (u * k) = χ k ∧ χ (k * u) = χ k)
    (hreg : ∀ d x, χ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E n) x (ratGL E n d))) ≠ 0 → IsRegD d) :
    IsTest F ∧ RegSupp F ∧ ∀ v, VCAt v F := by
  classical
  refine ⟨⟨hFc, hFs, U, hU, fun u hu g => ⟨?_, ?_⟩⟩, fun d x h => hreg d x ?_, fun v g hg => ?_⟩
  · simp only [hF, map_mul, pTest_gInf_finGL, pTest_gFin_finGL, one_mul, (hχU u hu _).1]
  · simp only [hF, map_mul, pTest_gInf_finGL, pTest_gFin_finGL, mul_one, (hχU u hu _).2]
  · rw [hF] at h; exact right_ne_zero_of_mul h
  · have hg' : gInf v g = 1 := hg
    have e : (fun d => F (embInf n v d * g)) =
        fun d => f v d * (c * (∏ w ∈ Finset.univ.erase v, f w (gInf w g)) * χ (gFin g)) := by
      funext d
      rw [hF, map_mul, pTest_gFin_embInf, one_mul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
      simp only [map_mul, pTest_gInf_embInf, Pi.mulSingle_eq_same, hg', mul_one]
      rw [Finset.prod_congr rfl fun w hw => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hw), one_mul]]
      ring
    exact e ▸ pTest_veryCusp_mul_const (hf v) _

theorem pTest_entry_le {y : G n} {R : ℝ} (h : lg y.val ≤ R) (i j : Fin n) :
    ‖y.val i j‖ ^ 2 ≤ Real.exp R ∧ ‖(y⁻¹).val i j‖ ^ 2 ≤ Real.exp R := by
  have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
  set S : ℝ := 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖y.val⁻¹ a b‖ ^ 2) with hS
  have h0 : 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖y.val⁻¹ a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hpos : 0 < S := by rw [hS]; linarith
  have hSR : S ≤ Real.exp R := (Real.log_le_iff_le_exp hpos).1 h
  have h1 : ‖y.val i j‖ ^ 2 + ‖y.val⁻¹ i j‖ ^ 2 ≤ ∑ b, (‖y.val i b‖ ^ 2 + ‖y.val⁻¹ i b‖ ^ 2) :=
    Finset.single_le_sum (f := fun b => ‖y.val i b‖ ^ 2 + ‖y.val⁻¹ i b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ b, (‖y.val i b‖ ^ 2 + ‖y.val⁻¹ i b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖y.val⁻¹ a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖y.val⁻¹ a b‖ ^ 2))
      (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ i)
  rw [hinv]
  constructor <;> nlinarith [sq_nonneg ‖y.val i j‖, sq_nonneg ‖y.val⁻¹ i j‖]

theorem pTest_posLog_sup_le {ι : Type} (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i, f i ≤ Real.exp R) : Real.posLog (⨆ i, f i) ≤ R := by
  have h := Real.posLog_le_posLog (Real.iSup_nonneg hf0) (Real.iSup_le hf (Real.exp_pos R).le)
  have e : Real.posLog (Real.exp R) = R := by simp [Real.posLog, hR]
  linarith

def pTestInfPart (x : GA E n) : ℝ := ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (x.val p.1 p.2)‖ ^ 2)

theorem pTest_logSizeM_le (x : GA E n) : logSizeM x.val ≤ pTestInfPart x + logSizeM (finGL E n (gFin x)).val := by
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), (⨆ p : Fin n × Fin n, ‖cW w (x.val p.1 p.2)‖) =
      ⨆ p : Fin n × Fin n, ‖cW w ((finGL E n (gFin x)).val p.1 p.2)‖ := fun w => by
    congr 1; funext p
    show ‖pLoc E w ((gFin x).val p.1 p.2)‖ = ‖pLoc E w ((gFin (finGL E n (gFin x))).val p.1 p.2)‖
    rw [pTest_gFin_finGL]
  have h0 : 0 ≤ ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((finGL E n (gFin x)).val p.1 p.2)‖ ^ 2) :=
    Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
  unfold logSizeM pTestInfPart
  rw [finsum_congr fun w => congrArg Real.posLog (hB w)]
  linarith

theorem pTest_inf_le (x : GA E n) {R : ℝ} (hR : 0 ≤ R) (h : ∀ v, lg (gInf v x).val ≤ R) :
    pTestInfPart x ≤ Fintype.card (InfinitePlace E) * R ∧ pTestInfPart x⁻¹ ≤ Fintype.card (InfinitePlace E) * R := by
  have key : ∀ y : GA E n, (∀ v, ∀ i j, ‖(gInf v y).val i j‖ ^ 2 ≤ Real.exp R) →
      pTestInfPart y ≤ Fintype.card (InfinitePlace E) * R := fun y hy => by
    unfold pTestInfPart
    calc _ ≤ ∑ _v : InfinitePlace E, R := Finset.sum_le_sum fun v _ =>
          pTest_posLog_sup_le _ (fun _ => by positivity) hR fun p => hy v p.1 p.2
      _ = _ := by simp
  refine ⟨key x fun v i j => (pTest_entry_le (h v) i j).1, key x⁻¹ fun v i j => ?_⟩
  rw [map_inv]; exact (pTest_entry_le (h v) i j).2

theorem pTest_logSize_le (x : GA E n) {R : ℝ} (hR : 0 ≤ R) (h : ∀ v, lg (gInf v x).val ≤ R) :
    logSize x ≤ 2 * Fintype.card (InfinitePlace E) * R + logSize (finGL E n (gFin x)) := by
  have h1 := pTest_logSizeM_le x
  have h2 := pTest_logSizeM_le x⁻¹
  have h3 := pTest_inf_le x hR h
  rw [map_inv, map_inv] at h2
  unfold logSize
  linarith [h3.1, h3.2]

theorem pTest_prod_ne {f : InfinitePlace E → G n → ℂ} {x : GA E n} (h : ∏ v, f v (gInf v x) ≠ 0) (v : InfinitePlace E) :
    f v (gInf v x) ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h v (Finset.mem_univ v)

theorem pTest_prod_finGL (f : InfinitePlace E → G n → ℂ) (u : GL (Fin n) (Af E)) (x : GA E n) :
    (∏ v, f v (gInf v (finGL E n u * x))) = ∏ v, f v (gInf v x) ∧
      (∏ v, f v (gInf v (x * finGL E n u))) = ∏ v, f v (gInf v x) := by
  simp only [map_mul, pTest_gInf_finGL, one_mul, mul_one, and_self]

theorem pTest_main {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (R r : ℝ)
    (U : Subgroup (Hf E a b)) (hR : 0 ≤ R)
    (ha : ∀ v, Continuous (fa v) ∧ VeryCusp (fa v) ∧ ∀ y, fa v y ≠ 0 → lg y.val ≤ R)
    (hb : ∀ v, Continuous (fb v) ∧ VeryCusp (fb v) ∧ ∀ y, fb v y ≠ 0 → lg y.val ≤ R)
    (hψs : HasCompactSupport ψ) (hUo : IsOpen (U : Set (Hf E a b)))
    (hψU : ∀ u ∈ U, ∀ h, ψ (u * h) = ψ h ∧ ψ (h * u) = ψ h)
    (hsz : ∀ h, ψ h ≠ 0 → logSize (finGL E a h.1) ≤ r ∧ logSize (finGL E b h.2) ≤ r)
    (hr₁ : ∀ d x h₂, ψ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) ≠ 0 → IsRegD d)
    (hr₂ : ∀ d x h₁, ψ (h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) ≠ 0 → IsRegD d) :
    IsTest2 (fun g : H E a b => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g))
      (2 * Fintype.card (InfinitePlace E) * R + r) ∧
    ∃ (U₁ : Subgroup (GL (Fin a) (Af E))) (U₂ : Subgroup (GL (Fin b) (Af E))), IsOpen (U₁ : Set (GL (Fin a) (Af E))) ∧
      IsOpen (U₂ : Set (GL (Fin b) (Af E))) ∧ ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₂, ∀ g : H E a b,
        (∏ v, fa v (gInf v (finGL E a u₁ * g.1))) * (∏ v, fb v (gInf v (finGL E b u₂ * g.2))) *
            ψ (hFin (finGL E a u₁ * g.1, finGL E b u₂ * g.2)) =
          (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g) ∧
        (∏ v, fa v (gInf v (g.1 * finGL E a u₁))) * (∏ v, fb v (gInf v (g.2 * finGL E b u₂))) *
            ψ (hFin (g.1 * finGL E a u₁, g.2 * finGL E b u₂)) =
          (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g) := by
  set φ : H E a b → ℂ := fun g => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g) with hφ
  have hψc : Continuous ψ := pTest_continuous_of_inv ψ U hUo fun u hu h => (hψU u hu h).1
  have hcont : Continuous φ := by
    refine (Continuous.mul ?_ ?_).mul (hψc.comp pTest_continuous_hFin)
    · exact continuous_finsetProd _ fun v _ => (ha v).1.comp ((pTest_continuous_gInf v).comp continuous_fst)
    · exact continuous_finsetProd _ fun v _ => (hb v).1.comp ((pTest_continuous_gInf v).comp continuous_snd)
  have hne : ∀ g, φ g ≠ 0 → (∀ v, fa v (gInf v g.1) ≠ 0) ∧ (∀ v, fb v (gInf v g.2) ≠ 0) ∧ ψ (hFin g) ≠ 0 :=
    fun g h => by
      obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 h
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h12
      exact ⟨pTest_prod_ne h1, pTest_prod_ne h2, h3⟩
  have hsupp : HasCompactSupport φ := by
    haveI : T2Space (H E a b) := inferInstanceAs (T2Space (GA E a × GA E b))
    let Ka : Set (InfinitePlace E → G a) := Set.pi Set.univ fun _ => {y : G a | lg y.val ≤ R}
    let Kb : Set (InfinitePlace E → G b) := Set.pi Set.univ fun _ => {y : G b | lg y.val ≤ R}
    have hKa : IsCompact Ka := isCompact_univ_pi fun _ => GlobalTheory.CompanionTheory.SobGL.isCompact_lg_le R
    have hKb : IsCompact Kb := isCompact_univ_pi fun _ => GlobalTheory.CompanionTheory.SobGL.isCompact_lg_le R
    let Φ : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b → H E a b := fun t =>
      (infGL E a (pTestY t.1.1) * finGL E a t.2.1, infGL E b (pTestY t.1.2) * finGL E b t.2.2)
    have hΦ : Continuous Φ :=
      (((pTest_continuous_infGL.comp pTest_continuous_pTestY).comp (continuous_fst.comp continuous_fst)).mul
          (pTest_continuous_finGL.comp (continuous_fst.comp continuous_snd))).prodMk
        (((pTest_continuous_infGL.comp pTest_continuous_pTestY).comp (continuous_snd.comp continuous_fst)).mul
          (pTest_continuous_finGL.comp (continuous_snd.comp continuous_snd)))
    have hK := ((hKa.prod hKb).prod hψs.isCompact).image hΦ
    refine HasCompactSupport.intro' hK hK.isClosed fun g hg => ?_
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hne g h
    refine hg ⟨((fun v => gInf v g.1, fun v => gInf v g.2), hFin g),
      ⟨⟨fun v _ => (ha v).2.2 _ (h1 v), fun v _ => (hb v).2.2 _ (h2 v)⟩, subset_tsupport _ h3⟩, ?_⟩
    exact Prod.ext (pTest_decomp g.1) (pTest_decomp g.2)
  have hU₁ : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin a) (Af E))) : Set (GL (Fin a) (Af E))) :=
    hUo.preimage (continuous_id.prodMk continuous_const)
  have hU₂ : IsOpen ((U.comap (MonoidHom.inr _ _) : Subgroup (GL (Fin b) (Af E))) : Set (GL (Fin b) (Af E))) :=
    hUo.preimage (continuous_const.prodMk continuous_id)
  refine ⟨⟨hcont, hsupp, fun g hg => ?_, fun g₂ => ?_, fun g₁ => ?_⟩, U.comap (MonoidHom.inl _ _),
    U.comap (MonoidHom.inr _ _), hU₁, hU₂, fun u₁ hu₁ u₂ hu₂ g => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hne g hg
    have e1 : logSize (finGL E a (gFin g.1)) ≤ r := (hsz _ h3).1
    have e2 : logSize (finGL E b (gFin g.2)) ≤ r := (hsz _ h3).2
    exact ⟨(pTest_logSize_le g.1 hR fun v => (ha v).2.2 _ (h1 v)).trans (by linarith),
      (pTest_logSize_le g.2 hR fun v => (hb v).2.2 _ (h2 v)).trans (by linarith)⟩
  · refine pTest_slice fa (fun v => (ha v).2.1) (fun k => ψ (k, gFin g₂)) (∏ v, fb v (gInf v g₂)) (fun g => φ (g, g₂))
      (fun g => by simp only [hφ, hFin]; ring) (hcont.comp (continuous_id.prodMk continuous_const))
      (pTest_supp_fst hsupp g₂) _ hU₁ (fun u hu k => ⟨?_, ?_⟩) fun d x h => hr₁ d x _ h
    · simpa [Prod.mk_mul_mk] using (hψU _ hu (k, gFin g₂)).1
    · simpa [Prod.mk_mul_mk] using (hψU _ hu (k, gFin g₂)).2
  · refine pTest_slice fb (fun v => (hb v).2.1) (fun k => ψ (gFin g₁, k)) (∏ v, fa v (gInf v g₁)) (fun g => φ (g₁, g))
      (fun g => by simp only [hφ, hFin]) (hcont.comp (continuous_const.prodMk continuous_id))
      (pTest_supp_snd hsupp g₁) _ hU₂ (fun u hu k => ⟨?_, ?_⟩) fun d x h => hr₂ d x _ h
    · simpa [Prod.mk_mul_mk] using (hψU _ hu (gFin g₁, k)).1
    · simpa [Prod.mk_mul_mk] using (hψU _ hu (gFin g₁, k)).2
  · have hu₁' : ((u₁, 1) : Hf E a b) ∈ U := hu₁
    have hu₂' : ((1, u₂) : Hf E a b) ∈ U := hu₂
    have k₁ : ψ ((u₁, 1) * ((1, u₂) * hFin g)) = ψ (hFin g) := by
      rw [(hψU _ hu₁' _).1, (hψU _ hu₂' _).1]
    have k₂ : ψ (hFin g * (1, u₂) * (u₁, 1)) = ψ (hFin g) := by
      rw [(hψU _ hu₁' _).2, (hψU _ hu₂' _).2]
    simp only [(pTest_prod_finGL fa u₁ g.1).1, (pTest_prod_finGL fb u₂ g.2).1, (pTest_prod_finGL fa u₁ g.1).2,
      (pTest_prod_finGL fb u₂ g.2).2]
    simp only [hFin, map_mul, pTest_gFin_finGL, Prod.mk_mul_mk, one_mul, mul_one] at k₁ k₂ ⊢
    exact ⟨by rw [k₁], by rw [k₂]⟩

theorem test2 : Test2 := fun E _ _ _ a b fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂ =>
  (pTest_main fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂).1

end PositivityTheory.Rg.BcB.CG
