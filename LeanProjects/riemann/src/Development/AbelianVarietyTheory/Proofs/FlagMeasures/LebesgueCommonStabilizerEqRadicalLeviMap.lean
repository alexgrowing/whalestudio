import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UEmbMulPEl

noncomputable section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.Swap

open GlobalTheory.Amp.Swap

variable {k r j : ℕ}

def extZ {α : Type} (P : α → Prop) [DecidablePred P] (E : Type) [AddCommGroup E] [Module ℝ E] :
    (Subtype P → E) →ₗ[ℝ] (α → E) where
  toFun x := fun a => if h : P a then x ⟨a, h⟩ else 0
  map_add' x y := by ext a; by_cases h : P a <;> simp [h]
  map_smul' c x := by ext a; by_cases h : P a <;> simp [h]

def resZ {α : Type} (P : α → Prop) (E : Type) [AddCommGroup E] [Module ℝ E] :
    (α → E) →ₗ[ℝ] (Subtype P → E) := LinearMap.funLeft ℝ E Subtype.val

theorem res_ext {α : Type} (P : α → Prop) [DecidablePred P] (E : Type) [AddCommGroup E] [Module ℝ E] (x : Subtype P → E) :
    resZ P E (extZ P E x) = x := by
  ext a; simp [resZ, extZ, LinearMap.funLeft_apply, a.2]

theorem ext_res {α : Type} (P : α → Prop) [DecidablePred P] (E : Type) [AddCommGroup E] [Module ℝ E] (y : α → E)
    (hy : ∀ a, ¬ P a → y a = 0) : extZ P E (resZ P E y) = y := by
  ext a; by_cases h : P a
  · simp [resZ, extZ, LinearMap.funLeft_apply, h]
  · simp [extZ, h, hy a h]

theorem ext_zero {α : Type} (P : α → Prop) [DecidablePred P] (E : Type) [AddCommGroup E] [Module ℝ E] (x : Subtype P → E)
    (a : α) (h : ¬ P a) : extZ P E x a = 0 := by simp [extZ, h]

theorem mp_ext {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (E : Type) [AddCommGroup E] [Module ℝ E]
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] (hP : ∀ a, P a) :
    MeasurePreserving (extZ P E) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : α => E) (Equiv.subtypeUnivEquiv hP)
  convert h using 1
  funext x a
  simp [extZ, hP a, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, Equiv.subtypeUnivEquiv]

abbrev STop (r j : ℕ) := ({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)

def extS (r j : ℕ) : STop r j →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) :=
  (extZ (fun p : UT r => j ≤ p.1.1.val) ℂ).prodMap (extZ (fun a : Fin r => j ≤ a.val) ℝ)

def resS (r j : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] STop r j :=
  (resZ (fun p : UT r => j ≤ p.1.1.val) ℂ).prodMap (resZ (fun a : Fin r => j ≤ a.val) ℝ)

abbrev extR (k r j : ℕ) := extZ (fun a : Fin r => j ≤ a.val) (Fin (k + 1) → ℂ)

theorem pTop_eq (q : PTop k r j) : pTop k r j q = pOf k r (extR k r j q.1, extS r j q.2) := rfl

theorem res_extS (s : STop r j) : resS r j (extS r j s) = s := by
  simp [resS, extS, res_ext]

def rowTop (k j : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) :=
  resZ (fun a : Fin r => j ≤ a.val) (Fin (k + 1) → ℂ) ∘ₗ rowLin k u ∘ₗ extR k r j

def skewTop (j : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (STop r j) :=
  resS r j ∘ₗ skewAct u ∘ₗ extS r j

theorem ext_rowTop (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (B : {a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) : extR k r j (rowTop k j u B) = rowLin k u (extR k r j B) := by
  refine ext_res (fun a : Fin r => j ≤ a.val) (Fin (k + 1) → ℂ) (rowLin k u (extR k r j B)) fun a ha => ?_
  funext i
  change ∑ c, star (u a c) * extR k r j B c i = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : j ≤ c.val
  · simp [hu a c ha hc]
  · rw [ext_zero (fun a : Fin r => j ≤ a.val) (Fin (k + 1) → ℂ) B c hc]; simp

theorem skew_ext_zero (s : STop r j) (c d : Fin r) (hc : ¬ j ≤ c.val) : skewLin r (extS r j s) c d = 0 := by
  change skewM (extZ (fun p : UT r => j ≤ p.1.1.val) ℂ s.1) (extZ (fun a : Fin r => j ≤ a.val) ℝ s.2) c d = 0
  unfold skewM
  split_ifs with h1 h2
  · exact ext_zero (fun p : UT r => j ≤ p.1.1.val) ℂ _ _ hc
  · rw [ext_zero]
    · simp
    · have : d.val < c.val := h2
      simp only; omega
  · rw [ext_zero (fun a : Fin r => j ≤ a.val) ℝ _ _ hc]; simp

theorem ext_skewTop (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (s : STop r j) : extS r j (skewTop j u s) = skewAct u (extS r j s) := by
  have h0 : ∀ a b : Fin r, ¬ j ≤ a.val → (u * skewLin r (extS r j s) * uᴴ) a b = 0 := by
    intro a b ha
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _
    by_cases hc : j ≤ c.val
    · simp [hu a c ha hc]
    · simp [skew_ext_zero s c d hc]
  have e : skewAct u (extS r j s) = coordLin r (u * skewLin r (extS r j s) * uᴴ) := by
    rw [← skew_skewAct, coord_skew]
  refine Prod.ext (ext_res (fun p : UT r => j ≤ p.1.1.val) ℂ (skewAct u (extS r j s)).1 fun p hp => ?_)
    (ext_res (fun a : Fin r => j ≤ a.val) ℝ (skewAct u (extS r j s)).2 fun a ha => ?_)
  · rw [e]; exact h0 _ _ hp
  · rw [e]
    change ((u * skewLin r (extS r j s) * uᴴ) a a).im = 0
    rw [h0 _ _ ha]; simp

theorem nil_rowLin (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsNilpotent (u - 1)) : IsNilpotent (rowLin k u - 1) := by
  obtain ⟨n, hn⟩ := hu
  have h1 : ∀ v w : Matrix (Fin r) (Fin r) ℂ, rowLin k (v * w) = rowLin k v * rowLin k w := by
    intro v w
    refine LinearMap.ext fun B => ?_
    ext a j
    simp only [rowLin, rowAct, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, star_sum,
      Finset.sum_mul, Finset.mul_sum, star_mul']
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : rowLin k (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine LinearMap.ext fun B => ?_
    ext a j
    simp [rowLin, rowAct, Matrix.one_apply, apply_ite (starRingEnd ℂ)]
  have h3 : rowLin k (u - 1) = rowLin k u - 1 := by
    rw [← h2]
    refine LinearMap.ext fun B => ?_
    ext a j
    simp [rowLin, rowAct, sub_mul]
  have h4 : ∀ m : ℕ, (rowLin k u - 1) ^ m = rowLin k ((u - 1) ^ m) := by
    intro m
    induction m with
    | zero => simp [h2]
    | succ m ih => rw [pow_succ, pow_succ, ih, h1, h3]
  refine ⟨n, ?_⟩
  rw [h4, hn]
  refine LinearMap.ext fun B => ?_
  ext a j
  simp [rowLin, rowAct]

theorem nil_conjLin (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsNilpotent (u - 1)) : IsNilpotent (conjLin u - 1) := by
  refine nil_mul (LinearMap.commute_mulLeft_right u uᴴ) ?_ ?_
  · have : LinearMap.mulLeft ℝ u - 1 = LinearMap.mulLeft ℝ (u - 1) := by
      refine LinearMap.ext fun S => ?_
      simp [sub_mul]
    rw [this, LinearMap.isNilpotent_mulLeft_iff]; exact hu
  · have : LinearMap.mulRight ℝ uᴴ - 1 = LinearMap.mulRight ℝ (uᴴ - 1) := by
      refine LinearMap.ext fun S => ?_
      simp [mul_sub]
    rw [this, LinearMap.isNilpotent_mulRight_iff]
    obtain ⟨n, hn⟩ := hu
    refine ⟨n, ?_⟩
    have := congrArg Matrix.conjTranspose hn
    simpa [Matrix.conjTranspose_pow] using this

theorem det_rowTop (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (hn : IsNilpotent (u - 1)) : LinearMap.det (rowTop k j u) = 1 :=
  det_eq_one (extR k r j) (Function.LeftInverse.injective (res_ext _ _)) _ (rowLin k u) (ext_rowTop u hu) (nil_rowLin u hn)

theorem det_skewTop (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (hn : IsNilpotent (u - 1)) : LinearMap.det (skewTop j u) = 1 :=
  det_eq_one (skewLin r ∘ₗ extS r j)
    ((Function.LeftInverse.injective coord_skew).comp (Function.LeftInverse.injective res_extS)) _ (conjLin u)
    (fun s => by
      simp only [LinearMap.comp_apply]
      rw [ext_skewTop u hu, skew_skewAct]; simp [conjLin, Matrix.mul_assoc]) (nil_conjLin u hn)

def topAct (u : Matrix (Fin r) (Fin r) ℂ) (q : PTop k r j) : PTop k r j := (rowTop k j u q.1, skewTop j u q.2)

theorem uEmb_mul_pTop (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (hd : IsUnit u.det) (q : PTop k r j) : uEmb k r u * pTop k r j q = pTop k r j (topAct u q) * uEmb k r u := by
  rw [pTop_eq, uEmb_mul_pOf u hd, pTop_eq]
  simp only [topAct, parAct, ext_rowTop u hu, ext_skewTop u hu]

theorem surj_of_det {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E)
    (h : LinearMap.det L = 1) : Function.Surjective L :=
  (LinearMap.equivOfDetNeZero L (by rw [h]; exact one_ne_zero)).surjective

theorem surj_topAct (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (hn : IsNilpotent (u - 1)) : Function.Surjective (topAct (k := k) (j := j) u) :=
  (surj_of_det _ (det_rowTop u hu hn)).prodMap (surj_of_det _ (det_skewTop u hu hn))

theorem mp_topAct (u : Matrix (Fin r) (Fin r) ℂ) (hu : ∀ a c : Fin r, ¬ j ≤ a.val → j ≤ c.val → u a c = 0)
    (hn : IsNilpotent (u - 1)) : MeasurePreserving (topAct (k := k) (j := j) u) volume volume := by
  haveI h0 : (volume : Measure (Fin (k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h1 : (volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (STop r j)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact (mp_of_det volume _ (det_rowTop u hu hn)).prod (mp_of_det volume _ (det_skewTop u hu hn))

theorem upperIn_zero (β : Fin r → ℕ) (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) (x : UTin β → ℂ)
    (a c : Fin r) (ha : ¬ j ≤ a.val) (hc : j ≤ c.val) : upperIn β x a c = 0 := by
  have h : a < c := by rw [Fin.lt_def]; omega
  have h' : ¬ β a = β c := fun e => ha ((hβ a c hc).1 e)
  simp [upperIn, upper, h, h']

theorem cont_topAct (β : Fin r → ℕ) :
    Continuous fun q : (UTin β → ℂ) × PTop k r j => topAct (upperIn β q.1) q.2 := by
  have h1 : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
      ((extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ q.1, (extR k r j q.2.1, extS r j q.2.2)) : (UT r → ℂ) × PPar k r) :=
    ((LinearMap.continuous_of_finiteDimensional _).comp continuous_fst).prodMk
      (((LinearMap.continuous_of_finiteDimensional _).comp continuous_snd.fst).prodMk
        ((LinearMap.continuous_of_finiteDimensional _).comp continuous_snd.snd))
  have h2 := (cont_parAct k r).comp h1
  exact ((resZ (fun a : Fin r => j ≤ a.val) (Fin (k + 1) → ℂ)).continuous_of_finiteDimensional.comp h2.fst).prodMk
    ((resS r j).continuous_of_finiteDimensional.comp h2.snd)

theorem cont_pTop : Continuous (pTop k r j) :=
  (cont_pOf k r).comp (((extR k r j).continuous_of_finiteDimensional.comp continuous_fst).prodMk
    ((extS r j).continuous_of_finiteDimensional.comp continuous_snd))

theorem pOf_inj : Function.Injective (pOf k r) := by
  intro q q' h
  have hB : q.1 = q'.1 := by
    funext b i
    have := congrFun (congrFun h (wI k r i)) (esI k r b)
    simpa [pOf, Rad.pEl_ws] using this
  have hS : skewLin r q.2 = skewLin r q'.2 := by
    ext a b
    have := congrFun (congrFun h (eI k r a)) (esI k r b)
    simp only [pOf, Rad.pEl_es, hB, sub_left_inj] at this
    exact this
  exact Prod.ext hB (Function.LeftInverse.injective coord_skew hS)

theorem pTop_inj : Function.Injective (pTop k r j) := by
  intro q q' h
  rw [pTop_eq, pTop_eq] at h
  have := Prod.ext_iff.1 (pOf_inj h)
  exact Prod.ext (Function.LeftInverse.injective (res_ext _ _) this.1) (Function.LeftInverse.injective res_extS this.2)

theorem pOf_mul_ee (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (pOf k r q * uEmb k r u) (eI k r a) (eI k r b) = u a b := by
  rw [Matrix.mul_apply, Rad.sum3]
  simp [pOf, Rad.pEl_ee, ← mI_eq, UEmb.u_ee, UEmb.u_me, UEmb.u_se]

theorem upper_inj : Function.Injective (upper (r := r)) := by
  intro x y h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [upper, p.2] using this

theorem range_eq_and_injective_parabolic_unipotent_product : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map (fun q => Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1))) ∧ Set.range (rEl k r j β) = Set.range (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ Function.Injective (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ (j = 0 → lebR0 k r j β = lebN k r) := by
  intro k r j β _ hβ
  have hz := upperIn_zero β hβ
  have hn : ∀ x : UTin β → ℂ, IsNilpotent (upperIn β x - 1) := fun x => nil_upper _
  have hd : ∀ x : UTin β → ℂ, IsUnit (upperIn β x).det := fun x => by simp [upperIn, UEmb.det_upper]
  have hr : ∀ q : (UTin β → ℂ) × PTop k r j,
      rEl k r j β q = pTop k r j (topAct (upperIn β q.1) q.2) * uEmb k r (upperIn β q.1) :=
    fun q => uEmb_mul_pTop _ (hz q.1) (hd q.1) q.2
  haveI s1 : SFinite (volume : Measure (STop r j)) := Measure.prod.instSFinite
  haveI s2 : SFinite (volume : Measure (PTop k r j)) := Measure.prod.instSFinite
  haveI b1 : BorelSpace (STop r j) := Prod.borelSpace
  haveI b2 : BorelSpace (PTop k r j) := Prod.borelSpace
  haveI b3 : BorelSpace ((UTin β → ℂ) × PTop k r j) := Prod.borelSpace
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hΦ : MeasurePreserving (fun q : (UTin β → ℂ) × PTop k r j => (q.1, topAct (upperIn β q.1) q.2)) volume volume :=
      (MeasurePreserving.id (volume : Measure (UTin β → ℂ))).skew_product
        (g := fun x q => topAct (k := k) (j := j) (upperIn β x) q)
        (cont_topAct β).measurable (Filter.Eventually.of_forall fun x => (mp_topAct _ (hz x) (hn x)).map_eq)
    have hG : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
        (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
      (cont_pTop.comp continuous_snd).matrix_mul ((cont_uEmb k r).comp
        ((extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ).continuous_of_finiteDimensional.comp continuous_fst))
    conv_rhs => rw [← hΦ.map_eq]
    rw [Measure.map_map hG.measurable hΦ.measurable, lebR0]
    congr 1
    funext q
    simp only [Function.comp]
    rw [hr]
  · ext m
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q.1, topAct (upperIn β q.1) q.2), (hr q).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨p, hp⟩ := surj_topAct (k := k) _ (hz q.1) (hn q.1) q.2
      exact ⟨(q.1, p), by rw [hr]; simp only [hp]⟩
  · intro q q' h
    simp only at h
    have h1 : upperIn β q.1 = upperIn β q'.1 := by
      ext a b
      have := congrFun (congrFun h (eI k r a)) (eI k r b)
      rwa [pTop_eq, pTop_eq, pOf_mul_ee, pOf_mul_ee] at this
    have h2 : q.1 = q'.1 := Function.LeftInverse.injective (res_ext _ _) (upper_inj h1)
    refine Prod.ext h2 (pTop_inj ?_)
    have h3 : uEmb k r (upperIn β q.1) * uEmb k r (upperIn β q.1)⁻¹ = 1 := by
      rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ (hd _), UEmb.uEmb_one]
    have := congrArg (· * uEmb k r (upperIn β q.1)⁻¹) h
    simpa only [← h1, Matrix.mul_assoc, h3, Matrix.mul_one] using this
  · rintro rfl
    haveI s3 : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := Measure.prod.instSFinite
    haveI s4 : SFinite (volume : Measure (PPar k r)) := Measure.prod.instSFinite
    have hΦ : MeasurePreserving (fun q : (UTin β → ℂ) × PTop k r 0 =>
        ((extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ q.1, (extR k r 0 q.2.1, extS r 0 q.2.2)) : (UT r → ℂ) × PPar k r))
        volume volume :=
      (mp_ext (fun p : UT r => β p.1.1 = β p.1.2) ℂ fun p => (hβ _ _ (Nat.zero_le _)).2 (Nat.zero_le _)).prod
        ((mp_ext (fun a : Fin r => 0 ≤ a.val) (Fin (k + 1) → ℂ) fun _ => Nat.zero_le _).prod
          ((mp_ext (fun p : UT r => 0 ≤ p.1.1.val) ℂ fun _ => Nat.zero_le _).prod
            (mp_ext (fun a : Fin r => 0 ≤ a.val) ℝ fun _ => Nat.zero_le _)))
    have hG : Continuous fun q : (UT r → ℂ) × PPar k r =>
        (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) :=
      ((cont_uEmb k r).comp continuous_fst).matrix_mul ((cont_pOf k r).comp continuous_snd)
    rw [lebN, ← hΦ.map_eq, Measure.map_map hG.measurable hΦ.measurable, lebR0]
    rfl

end GlobalTheory.DegVol.Swap
