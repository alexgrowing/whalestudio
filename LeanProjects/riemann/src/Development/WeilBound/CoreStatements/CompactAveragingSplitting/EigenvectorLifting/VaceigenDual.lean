import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

noncomputable section

namespace PositivityTheory.ThK.Vac

open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem eq_liftV {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : a = liftV v (evFin F v a) :=
  (GlobalTheory.LatVacArith.eq_liftV_of_at ha).trans (GlobalTheory.LatVacArith.liftV_one_mul v a)

theorem liftV_mul (v : Pl F) (t : Fv F v) (a : AF F) : liftV v t * a = liftV v (t * evFin F v a) :=
  (eq_liftV (GlobalTheory.VacAny.at_mul_right (at_liftV v t) a)).trans (by rw [map_mul, evFin_liftV])

theorem mem_int_of_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) (c : Fv F v)
    (h : ∀ t ∈ codiff F, ∀ a ∈ v.adicCompletionIntegers F, ψ (liftV v (a * (algebraMap F (Fv F v) t * c))) = 1) :
    c ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ t ∈ codiff F, algebraMap F (Fv F v) t * c ∈ GlobalTheory.Idele.localIdeal v (codiff F) := fun t ht => by
    have hmem : singleFin v (algebraMap F (Fv F v) t * c) ∈ GlobalTheory.Idele.adelicIdeal (codiff F) := by
      rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ)]
      intro α hα
      have e : α * singleFin v (algebraMap F (Fv F v) t * c) = singleFin v (α v * (algebraMap F (Fv F v) t * c)) := by
        apply af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]
          rfl
        · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact h t ht _ (hα v)
    have h2 := hmem v
    rwa [show (singleFin v (algebraMap F (Fv F v) t * c)) v = _ from evalV_singleFin_self v _] at h2
  have h2 : ∀ x ∈ GlobalTheory.Idele.localIdeal v (codiff F), x * c ∈ GlobalTheory.Idele.localIdeal v (codiff F) := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact h1 t ht
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hx : Valued.v (algebraMap F (Fv F v) (π ^ FractionalIdeal.count F v (codiff F))) =
      WithZero.exp (-FractionalIdeal.count F v (codiff F)) := by
    rw [GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have h3 := (GlobalTheory.Idele.mem_localIdeal_iff codiff_ne_zero v _).1
    (h2 _ ((GlobalTheory.Idele.mem_localIdeal_iff codiff_ne_zero v _).2 hx.le))
  rw [map_mul, hx] at h3
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (mul_le_iff_le_one_right (WithZero.exp_pos)).1 h3

theorem isUnit_det_of_hasSig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨e, A, hA⟩ := h
  have h1 : Aᵀ * (M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.fromBlocks_multiply]
    simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [e])).1 h1
  rw [Matrix.mul_assoc] at h2
  exact (Matrix.isUnit_det_of_right_inverse h2).ne_zero

theorem herm_det {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsUnit X.J.det := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have := isUnit_det_of_hasSig (h.sig w)
  refine isUnit_iff_ne_zero.2 fun h0 => this ?_
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem skew_det {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsSkew σ B r s) : IsUnit X.J.det := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have := isUnit_det_of_hasSig (h.sig w)
  refine isUnit_iff_ne_zero.2 fun h0 => this ?_
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem cA_cA (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_incl (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

theorem trace_incl (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def incV (y : Fin d → E) : Fin d → AE F E := fun i => inclR (F := F) (AF F) (y i)

def trF (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) E) (y : Fin d → E) : (Fin d → AE F E) →ₗ[AF F] AF F where
  toFun w := Algebra.trace (AF F) (AE F E) (∑ l, inclR (F := F) (AF F) ((y ᵥ* J) l) * cA σ (w l))
  map_add' w w' := by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' a w := by simp only [Pi.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, RingHom.id_apply]

theorem form_eq (J : Matrix (Fin d) (Fin d) E) (y x : Fin d → E) : form σ J y x = ∑ l, (y ᵥ* J) l * σ (x l) := by
  rw [form, Matrix.dotProduct_mulVec]; rfl

theorem trF_incV (J : Matrix (Fin d) (Fin d) E) (y x : Fin d → E) :
    trF σ J y (incV x) = algebraMap F (AF F) (Algebra.trace F E (form σ J y x)) := by
  rw [← trace_incl, form_eq, map_sum]
  simp only [map_mul]
  rfl

theorem trF_smul (J : Matrix (Fin d) (Fin d) E) (t : F) (y : Fin d → E) (w : Fin d → AE F E) :
    trF σ J (algebraMap F E t • y) w = algebraMap F (AF F) t * trF σ J y w := by
  have e : inclR (F := F) (AF F) (algebraMap F E t) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) t) :=
    ((Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes t).trans (IsScalarTower.algebraMap_apply _ _ _ _)
  rw [← smul_eq_mul, ← map_smul]
  change Algebra.trace _ _ _ = Algebra.trace _ _ _
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, map_mul, e, Pi.smul_apply, map_smul, Algebra.smul_def]
  ring

theorem span_incV (w : Fin d → AE F E) : w ∈ Submodule.span (AF F) (Set.range (incV (F := F) (E := E) (d := d))) := by
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun j _ => ?_
  induction w j using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact zero_mem _
  | tmul a e =>
    have : (Pi.single j (a ⊗ₜ[F] e) : Fin d → AE F E) = a • incV (Pi.single j e) := by
      ext i
      by_cases h : i = j
      · subst h
        simp only [incV, Pi.single_eq_same, Pi.smul_apply]
        change _ = a • ((1 : AF F) ⊗ₜ[F] e)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp [incV, Pi.single_eq_of_ne h]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add x y hx hy => rw [Pi.single_add]; exact add_mem hx hy

theorem exists_tr_rep (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin d) (Fin d) E} (hJ : IsUnit J.det) (f : (Fin d → E) →ₗ[F] F) :
    ∃ u, ∀ x, f x = Algebra.trace F E (form σ J u x) := by
  have h : ∀ j : Fin d, ∃ b : E, ∀ e, Algebra.trace F E (b * e) = f (Pi.single j (σ e)) := fun j => by
    obtain ⟨b, hb⟩ := ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).surjective
      (f ∘ₗ LinearMap.single F (fun _ => E) j ∘ₗ σ.toLinearMap)
    exact ⟨b, fun e => LinearMap.congr_fun hb e⟩
  choose b hb using h
  refine ⟨b ᵥ* J⁻¹, fun x => ?_⟩
  rw [form_eq, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ, Matrix.vecMul_one, map_sum]
  simp only [hb, hσ]
  rw [← map_sum, Finset.univ_sum_single]

theorem mem_latW {B : Base F E} (hB : B.IsGood σ) {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B r s) (v : Pl F)
    {w : Fin d → AE F E} (hw : At (evFin F v) w)
    (h : ∀ y ∈ W.L, ∀ a ∈ v.adicCompletionIntegers F, B.ψ (liftV v a * trF σ W.J y w) = 1) : w ∈ latW W v := by
  have hσ := sigma_sigma hB.cm
  have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E
      (W.L : Set (Fin d → E)) x (hW.lat.span_eq_top ▸ Submodule.mem_top)
    obtain ⟨_, k, hk, rfl⟩ := t
    rw [Submodule.span_eq] at ht
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have ht' : (k : F) • x ∈ W.L := by
      rw [Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]; exact ht
    rw [← inv_smul_smul₀ hk0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht'))
  choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)
  have hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i) := fun z => by
    have hz := span_incV z
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      simp only [trF_incV, ← hu]
      ext j
      conv_lhs => rw [hid x]
      simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]
      exact Finset.sum_congr rfl fun i _ =>
        map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, ← hx, ← hy]
    | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
  rw [hdec w]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩
  · rw [← map_smul, hw a ha, map_zero]
  · refine mem_int_of_psi hB.std v _ fun t ht a ha => ?_
    have hm : algebraMap F E t • u i ∈ W.L := (hW.dual _).2 fun x hx o => by
      let o' : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩
      obtain ⟨c, hc⟩ := hf i _ (W.L.smul_mem o' hx)
      have e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x) := by
        rw [form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : (o' • x) l = σ o * x l := rfl
        rw [this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]
      obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _
        ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
      rw [Algebra.traceForm_apply] at hk
      rw [← hk]
      exact isIntegral_algebraMap
    have := h _ hm a ha
    rwa [trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes] at this

theorem vecMulVec_mem {X : Spc F E n} {W : Spc F E d} {v : Pl F} {x : Fin n → E} (hx : x ∈ X.L) {w : Fin d → AE F E}
    (hw : w ∈ latW W v) : Matrix.vecMulVec (incV x) w ∈ latAtV X W v := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, y, hy, ?_⟩
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply]
  | zero =>
    have : Matrix.vecMulVec (incV (F := F) x) (0 : Fin d → AE F E) = 0 := by ext i j; exact mul_zero _
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.vecMulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.vecMulVec_neg]; exact neg_mem hy

theorem symp_vecMulVec (hσ : ∀ x, σ (σ x) = x) (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (x : Fin n → E) (y : Fin d → E) (z : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB) (incM F (Matrix.vecMulVec x y)) z =
      -trF σ JB y (incV (fun k => σ ((x ᵥ* JA) k)) ᵥ* z) := by
  rw [symp, neg_one_mul, map_neg]
  change _ = -Algebra.trace _ _ _
  congr 2
  simp only [hTens, incM, incV, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    cA_incl, hσ, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]; enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]; enter [2, i]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mem_latAtV {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (v : Pl F) {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ z) = 1) : z ∈ latAtV X W v := by
  have hσ := sigma_sigma hB.cm
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 E) E X.L hX.lat.fg hX.lat.span_eq_top
  let a : Fin m → Fin n → E := fun i k => f i (Pi.single k 1)
  let u : Fin m → Fin n → E := fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹
  have hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k) := fun i => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]
  have huL : ∀ i, u i ∈ X.L := fun i => (hX.dual _).2 fun x hx => by
    obtain ⟨c, hc⟩ := hf i x hx
    have e : form σ X.J (u i) x = σ (f i x) := by
      rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [this]
    rw [e, ← hc]
    exact (RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)
  have hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z) := by
    ext p l
    have e : ∀ k, ∑ i, incV (F := F) (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by
      have := congrFun (hid (Pi.single k 1)) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, e]
    exact (congrFun (congrFun (Matrix.one_mul z) p) l).symm
  rw [hdec]
  refine sum_mem fun i _ => vecMulVec_mem (hg i) (mem_latW hB hW v (fun c hc => ?_) fun y hy c hc => ?_)
  · rw [← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]
  · have := h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy, rfl⟩))
    rw [GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu] at this
    simpa only [hσ, mul_one, mul_neg, neg_neg] using this

end PositivityTheory.ThK.Vac
