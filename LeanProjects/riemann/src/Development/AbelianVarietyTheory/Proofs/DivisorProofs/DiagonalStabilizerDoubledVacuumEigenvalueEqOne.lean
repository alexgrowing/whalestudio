import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegel
open MeasureTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_eq_one_of_eigen (hF : IsTotallyReal F) {κ G : Type} [Fintype κ] [Group G]
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (h : IsUnitaryOn (adeleClass F) om) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {g : G} {c : ℂ} (hg : om g Φ = c • Φ) : ‖c‖ = 1 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  let ν : Measure (κ → AF F) := Measure.addHaar
  have e := h ν inferInstance g Φ hΦ
  rw [hg] at e
  refine norm_eq_one_of_lintegral_eq e ?_ ?_
  · intro hz
    rw [lintegral_eq_zero_iff (by fun_prop)] at hz
    have h1 : Φ =ᵐ[ν] 0 := hz.mono fun x hx => by simpa using hx
    exact h0 ((Continuous.ae_eq_iff_eq ν hc continuous_const).1 h1)
  · have h2 : Integrable (fun x => Φ x * Φ x) ν :=
      (hi ν inferInstance).mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have h3 := h2.2
    simp only [HasFiniteIntegral, enorm_mul] at h3
    simpa only [pow_two] using h3.ne

variable (F) in
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem lDiag_box_ne_zero (hF : IsTotallyReal F) {κ : Type} [Fintype κ] {Ψ : (κ → AF F) → ℂ}
    (hΨ : Ψ ∈ schA F κ) (h0 : Ψ ≠ 0) : DiagForm.lDiag F κ (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI := DiagForm.measAf (F := F)
  haveI := DiagForm.borelAf (F := F)
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F κ Ψ hΨ)
  have hi := DiagForm.integrable_resD hS
  have hc : Continuous Ψ := by
    letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    exact (GlobalTheory.SplitSvN.schA_facts hF hΨ).1
  have hg : Continuous (DiagForm.glue : DiagForm.Vi F κ × DiagForm.Vf F κ → κ → AF F) := by
    refine continuous_pi fun i => Continuous.prodMk ?_ ((continuous_apply i).comp continuous_snd)
    exact (continuous_ofMixed F).comp ((continuous_apply i).comp ((DiagForm.eI F κ).continuous.comp continuous_fst))
  have e : DiagForm.resD F κ (boxFun Ψ fun x => star (Ψ x)) =
      fun p => ((Complex.normSq (Ψ (DiagForm.glue p)) : ℝ) : ℂ) := funext fun p => Complex.mul_conj _
  rw [DiagForm.lDiag, LinearMap.comp_apply, DiagForm.Lext_apply _ hi, e, integral_complex_ofReal,
    Ne, Complex.ofReal_eq_zero]
  intro h1
  rw [e] at hi
  have hi' : Integrable (fun p => Complex.normSq (Ψ (DiagForm.glue p))) (DiagForm.mu F κ) := by
    simpa using hi.re
  have h2 := (integral_eq_zero_iff_of_nonneg (fun p => Complex.normSq_nonneg _) hi').1 h1
  haveI : (DiagForm.mu F κ).IsOpenPosMeasure := by unfold DiagForm.mu; infer_instance
  have h3 := (Continuous.ae_eq_iff_eq _ (Complex.continuous_normSq.comp (hc.comp hg)) continuous_const).1 h2
  refine h0 (funext fun x => ?_)
  have h4 := Complex.normSq_eq_zero.1 (congrFun h3 (0 + DiagForm.shiftOf x))
  rw [Function.comp_apply, DiagForm.glue_add_shiftOf] at h4
  have h5 : DiagForm.glue (0 : DiagForm.Vi F κ × DiagForm.Vf F κ) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (DiagForm.eI F κ 0 i) = 0
    rw [map_zero, Pi.zero_apply, map_zero]
  rwa [h5, zero_add] at h4

variable (F) in

def piE (P : HeightOneSpectrum (𝓞 E)) : AE F E →+* P.adicCompletion E :=
  (evalV E P).toRingHom.comp ((finAdEquiv F E).toRingHom.comp (finTens F E))

theorem piE_tmul (P : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : E) :
    piE F P (a ⊗ₜ[F] x) = complMap rfl (evFin F (P.under (𝓞 F)) a) * algebraMap E _ x := rfl

theorem piE_algebraMap {P : HeightOneSpectrum (𝓞 E)} {v : Pl F} (h : P.under (𝓞 F) = v) (a : AF F) :
    piE F P (algebraMap (AF F) (AE F E) a) = complMap h (evFin F v a) := by
  subst h
  exact (piE_tmul P a 1).trans (by rw [map_one, mul_one])

theorem piE_inclR (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    piE F P (inclR (F := F) (AF F) x) = algebraMap E _ x :=
  (piE_tmul P 1 x).trans (by rw [map_one, map_one, one_mul])

theorem val_det_le {K Γ n : Type} [CommRing K] [LinearOrderedCommMonoidWithZero Γ] (u : Valuation K Γ) [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {b : Γ} (h : ∀ i j, u (M i j) ≤ b) : u M.det ≤ b ^ Fintype.card n := by
  rw [Matrix.det_apply]
  refine u.map_sum_le fun s _ => ?_
  have e : ∀ x : K, u (Equiv.Perm.sign s • x) = u x := fun x => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]
  rw [e, map_prod]
  exact Finset.prod_le_pow_card _ _ _ fun i _ => h _ _

theorem val_det_le_one {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (t : Matrix (Fin d) (Fin d) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) : Valued.v (piE F w t.det) ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := hL.fg
  let b : WithZero (Multiplicative ℤ) :=
    (s ×ˢ (Finset.univ : Finset (Fin d))).sup fun q => Valued.v (algebraMap E (w.adicCompletion E) (q.1 q.2))
  have hLb : ∀ y ∈ W.L, ∀ i, Valued.v (algebraMap E (w.adicCompletion E) (y i)) ≤ b := by
    intro y hy i
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Finset.le_sup (f := fun q : (Fin d → E) × Fin d => Valued.v (algebraMap E (w.adicCompletion E) (q.1 q.2)))
        (b := (y, i)) (Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.add_apply, map_add]; exact Valued.v.map_add_le hx hy
    | smul c x _ hx =>
      have hc : Valued.v (algebraMap E (w.adicCompletion E) (c : E)) ≤ 1 :=
        GlobalTheory.AdeleBaseChange.algebraMap_int_mem c w
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul]
      exact (mul_le_mul' hc hx).trans_eq (one_mul _)
  have hΛ : ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ i, Valued.v (piE F w (z i)) ≤ b := by
    intro z hz i
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, piE_algebraMap hw, piE_inclR]
      exact (mul_le_mul' (complMap_mem hw ha) (hLb y hy i)).trans_eq (one_mul _)
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.add_apply, map_add]; exact Valued.v.map_add_le hx hy
    | neg x _ hx => rw [Pi.neg_apply, map_neg, Valuation.map_neg]; exact hx
  have hc : ∀ j : Fin d, ∃ c : E, c ≠ 0 ∧ Pi.single j c ∈ W.L := fun j => by
    have h1 : (Pi.single j 1 : Fin d → E) ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ _ h1
    rw [Submodule.span_eq] at hc
    refine ⟨((c : 𝓞 E) : E), by simpa using nonZeroDivisors.coe_ne_zero c, ?_⟩
    convert hc using 1
    funext i
    by_cases hi : i = j
    · subst hi; simp [Submonoid.smul_def, Algebra.smul_def]
    · simp [hi]
  choose c hc0 hc using hc
  have hpow : ∀ n : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ n) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  set D := Valued.v (piE F w t.det) with hD
  let k : WithZero (Multiplicative ℤ) := Valued.v (∏ j, algebraMap E (w.adicCompletion E) (c j))
  have hk : k ≠ 0 := (Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hc0 j)
  have key : ∀ n : ℕ, D ^ n * k ≤ b ^ Fintype.card (Fin d) := fun n => by
    have h1 := val_det_le (Valued.v : Valuation (w.adicCompletion E) _)
      ((t ^ n).map (piE F w) * Matrix.diagonal fun j => algebraMap E (w.adicCompletion E) (c j)) (b := b) (fun i j => by
        have hz : (GlobalTheory.LatVac.liftV v 1 • fun i => inclR (F := F) (AF F) ((Pi.single j (c j) : Fin d → E) i)) ∈
            GlobalTheory.InertSph.latAt W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v 1, by rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _,
            _, hc j, rfl⟩
        have h2 := hΛ _ (hpow n _ hz) i
        rw [Matrix.mul_diagonal]
        convert h2 using 2
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j (fun l _ hl => by simp [hl]) (by simp), map_mul,
          Pi.smul_apply, Algebra.smul_def, map_mul, piE_algebraMap hw, GlobalTheory.LatVac.evFin_liftV, map_one, one_mul,
          piE_inclR, Pi.single_eq_same]
        rfl)
    rw [Matrix.det_mul, Matrix.det_diagonal, map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_pow,
      map_pow, map_pow] at h1
    exact h1
  by_contra h
  obtain ⟨n, hn⟩ := MulArchimedean.arch (D * b ^ Fintype.card (Fin d) / k) (lt_of_not_ge h)
  rw [div_le_iff₀ (zero_lt_iff.2 hk)] at hn
  have h0 : 0 < b ^ Fintype.card (Fin d) := (zero_lt_iff.2 hk).trans_le (by simpa using key 0)
  exact h ((mul_le_iff_le_one_left h0).1 (hn.trans (key n)))

theorem chr_det_eq_one {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Formalism.UG.IsInertAt F E v w) {χ : Chr F E} (hχ : UnrAt χ w) (t : GL (Fin d) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  classical
  have hu := under_eq_of_isInertAt hw
  set δ := Matrix.GeneralLinearGroup.det t with hδ
  let y : (w.adicCompletion E)ˣ := Units.map (piE F w).toMonoidHom δ
  have hy : Formalism.L2.Host.IsUnitAt w y := by
    have a1 : Valued.v (y : w.adicCompletion E) ≤ 1 := val_det_le_one W hL hu _ fun z hz => (ht z hz).1
    have a2 : Valued.v ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
      have := val_det_le_one W hL hu _ fun z hz => (ht z hz).2
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this
      exact this
    have h0 : 0 < Valued.v (y : w.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 y.ne_zero)
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0] at a2
    exact le_antisymm a1 a2
  have hN := h1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have hφ : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R),
      φ (algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) = 0 → φ (δ : AE F E) = 1 := by
    intro R _ φ hφ
    have : φ.mapMatrix (t : Matrix (Fin d) (Fin d) (AE F E)) = φ.mapMatrix 1 := by
      ext i j
      have h2 := congrArg φ (congrFun (congrFun hN i) j)
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, map_sub, map_sub, map_one, map_one, hφ, sub_zero, one_mul,
        Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h2
      exact h2
    rw [hδ, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, this, map_one, Matrix.det_one]
  have e : δ = locIdele F w y := by
    refine eq_locIdele (hφ _ (TensorProduct.zero_tmul _ _)) (FiniteAdeleRing.ext _ fun P => ?_)
    change piE F P δ = _
    rw [GlobalTheory.CMVal.single_apply]
    by_cases hP : P = w
    · subst hP; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hP]
      refine hφ _ ?_
      have hPv : P.under (𝓞 F) ≠ v := fun h => hP (by
        refine (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top ?_)).symm
        rw [← show Ideal.map _ _ = w.asIdeal from hw, Ideal.map_le_iff_le_comap, ← h]
        exact le_rfl)
      rw [piE_algebraMap rfl]
      exact (congrArg _ (evalV_singleFin_ne hPv 1)).trans (map_zero _)
  rw [e]
  exact Circle.ext (congrArg Units.val (hχ y hy))

theorem eigen_eq_one_of_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin (a + a')) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.W) (s : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) = (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin (a + a') → AE F E, (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))) *
          ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hβ : X.β (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one G.W hT.geo.hW.lat hw (hT.chars.unrβ w fun h => hv ?_) t (fun u hu => ?_) fun z hz => ?_
    · rw [← under_eq_of_isInertAt hw]; exact h
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
          (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (u • ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

end GlobalTheory.DblVacSiegel
