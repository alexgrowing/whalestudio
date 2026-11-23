import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def torepUnit (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩

lemma torep_inUJ (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem hg.1
  unfold inUJ
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

def torepK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨torepUnit ε hg, torep_inUJ ε hg⟩, hg⟩

lemma toMK_torepK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    toMK (torepK ε hg) = g := rfl

lemma torepK_toMK (ε : Fin n → Bool) (k : KG ε) : torepK ε k.2 = k := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

lemma continuous_torepK (ε : Fin n → Bool) :
    Continuous (fun x : Kset ε => torepK ε x.2) := by
  unfold torepK
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_star.comp continuous_subtype_val

open Classical in

def torepSig {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (g : Matrix (Fin n) (Fin n) ℂ) :
    T.V →L[ℂ] T.V :=
  if h : g ∈ Kset ε then T.op (torepK ε h) else 1

lemma torepSig_of_mem {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε) : torepSig T g = T.op (torepK ε hg) := by
  unfold torepSig
  rw [dif_pos hg]

lemma torepSig_toMK {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    torepSig T (toMK k) = T.op k := by
  rw [torepSig_of_mem T k.2, torepK_toMK]

lemma torep_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k k' : KG ε) :
    T.op (k * k') = (T.op k).comp (T.op k') := by
  show ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma torep_one_mem (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε := by
  unfold Kset
  exact ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

private lemma kset_mul_lemma {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  have hg2 : g * Jm ε = Jm ε * g := hg.2
  have hh2 : h * Jm ε = Jm ε * h := hh.2
  unfold Kset
  exact ⟨mul_mem hg.1 hh.1, by rw [Matrix.mul_assoc, hh2, ← Matrix.mul_assoc, hg2, Matrix.mul_assoc]⟩

private lemma torepK_mul_lemma_2 (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) (hgh : g * h ∈ Kset ε) : torepK ε hgh = torepK ε hg * torepK ε hh := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

lemma torep_isURepOn {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (torepSig T) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [torepSig_of_mem T (torep_one_mem ε)]
    have h1 : torepK ε (torep_one_mem ε) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rfl
    rw [h1]
    simp [KType.op]
  · intro a ha b hb
    have ha' : a ∈ Kset ε := ha
    have hb' : b ∈ Kset ε := hb
    rw [torepSig_of_mem T (kset_mul_lemma ha' hb'), torepSig_of_mem T ha', torepSig_of_mem T hb',
      torepK_mul_lemma_2 ε ha' hb', torep_op_mul]
  · intro g hg v
    have hg' : g ∈ Kset ε := hg
    rw [torepSig_of_mem T hg']
    exact ContinuousLinearMap.norm_map_of_mem_unitary (T.τ _).2 v
  · intro v
    refine continuousOn_iff_continuous_restrict.2 ?_
    have hc : Continuous fun x : Kset ε => T.op (torepK ε x.2) :=
      (continuous_subtype_val.comp T.cont).comp (continuous_torepK ε)
    have hc2 : Continuous fun x : Kset ε => T.op (torepK ε x.2) v := hc.clm_apply continuous_const
    refine hc2.congr fun x => ?_
    exact (congrArg (fun f => f v) (torepSig_of_mem T x.2)).symm

lemma torep_exp_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (v : V) (c : ℂ) (h : A v = c • v) :
    NormedSpace.exp A v = NormedSpace.exp c • v := by
  have hpow : ∀ m : ℕ, (A ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V v)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext m
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, hpow,
    smul_smul, smul_eq_mul]

lemma torep_diag_sum (d : Fin n → ℂ) :
    Matrix.diagonal d = ∑ a, d a • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.single_apply, Matrix.diagonal_apply]
  · rw [Matrix.diagonal_apply_ne _ h]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [Matrix.smul_apply, Matrix.single_apply, if_neg (fun h' => h (h'.1.symm.trans h'.2)), smul_zero]

lemma torep_inK_diag (ε : Fin n → Bool) (d : Fin n → ℂ) (hd : ∀ a, star (d a) = -d a) :
    inK ε (Matrix.diagonal d) := by
  refine ⟨?_, ?_⟩
  · simp only [inG, Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    rw [show (0 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => 0) from Matrix.diagonal_zero.symm]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [hd a]
    ring
  · simp only [Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma torep_exp_diag (d : Fin n → ℂ) :
    NormedSpace.exp (Matrix.diagonal d) = Matrix.diagonal (fun a => Complex.exp (d a)) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext a
  have e1 : NormedSpace.exp d a = NormedSpace.exp (d a) := by
    first
    | exact NormedSpace.map_exp (Pi.evalRingHom (fun _ : Fin n => ℂ) a) (continuous_apply a) d
    | exact NormedSpace.Pi.exp_apply d a
    | exact NormedSpace.exp_apply d a
  rw [e1, Complex.exp_eq_exp_ℂ]

private lemma diag_mem_lemma_3 {ε : Fin n → Bool} (f : Fin n → ℂ) (hf : ∀ b, f b * star (f b) = 1) :
    Matrix.diagonal f ∈ Kset ε := by
  unfold Kset
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hf b
  · simp only [Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext b
    ring

private lemma expI_lemma_4 (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * star (Complex.exp ((x : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add,
    show (x : ℂ) * Complex.I + (x : ℂ) * -Complex.I = 0 by ring, Complex.exp_zero]

private lemma torepK_congr_lemma_6 (ε : Fin n → Bool) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hg' : g' ∈ Kset ε) (h : g = g') : torepK ε hg = torepK ε hg' := by
  subst h
  rfl

private lemma torepK_one_lemma_7 (ε : Fin n → Bool) : torepK ε (torep_one_mem ε) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

private lemma oneParam_lemma_5 {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (F : ℝ → A) (D : A)
    (hadd : ∀ s t, F (s + t) = F s * F t) (h0 : F 0 = 1) (hD : HasDerivAt F D 0) (t : ℝ) :
    F t = NormedSpace.exp (t • D) := by
  have hder : ∀ u, HasDerivAt F (F u * D) u := by
    intro u
    have h1 : HasDerivAt (fun x => F (x - u)) D u :=
      HasDerivAt.comp_sub_const u u (by rw [sub_self]; exact hD)
    have h2 := h1.const_mul (F u)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show F x = F u * F (x - u)
    rw [← hadd]
    congr 1
    ring
  have hcomm : ∀ u, F u * D = D * F u := by
    intro u
    have e1 : HasDerivAt (fun h => F u * F h) (F u * D) 0 := hD.const_mul (F u)
    have e2 : HasDerivAt (fun h => F h * F u) (D * F u) 0 := hD.mul_const (F u)
    have e3 : (fun h => F u * F h) = fun h => F h * F u := funext fun h => by
      rw [← hadd, ← hadd, add_comm]
    rw [e3] at e1
    exact e1.unique e2
  have key : ∀ (P Q : ℝ → A) (X Y : A), (∀ u, HasDerivAt P (P u * X) u) → (∀ u, HasDerivAt Q (Y * Q u) u) →
      (∀ u, P u * X * Q u + P u * (Y * Q u) = 0) → P 0 * Q 0 = 1 → ∀ u, P u * Q u = 1 := by
    intro P Q X Y hP hQ hPQ h00 u
    have hG : ∀ u, HasDerivAt (fun u => P u * Q u) 0 u := by
      intro u
      have h := (hP u).mul (hQ u)
      convert h using 1
      all_goals first
        | rfl
        | exact (hPQ u).symm
    have h := is_const_of_deriv_eq_zero (f := fun u => P u * Q u) (fun x => (hG x).differentiableAt)
      (fun x => (hG x).deriv) u 0
    rw [show P u * Q u = P 0 * Q 0 from h, h00]
  have hE1 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -D)) (NormedSpace.exp (u • -D) * (-D)) u := by
    intro u
    first
    | exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-D) u
    | exact hasDerivAt_exp_smul_const (-D) u
  have hE2 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -D)) ((-D) * NormedSpace.exp (u • -D)) u := by
    intro u
    first
    | exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) u
    | exact hasDerivAt_exp_smul_const' (-D) u
  have hE3 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • D)) (NormedSpace.exp (u • D) * D) u := by
    intro u
    first
    | exact hasDerivAt_exp_smul_const (𝕂 := ℝ) D u
    | exact hasDerivAt_exp_smul_const D u
  have hder' : ∀ u, HasDerivAt F (D * F u) u := fun u => by rw [← hcomm u]; exact hder u
  have h1 := key (fun u : ℝ => NormedSpace.exp (u • -D)) F (-D) D hE1 hder'
    (fun u => by simp only [mul_neg, neg_mul, mul_assoc, neg_add_cancel]) (by simp [h0]) t
  have h2 := key (fun u : ℝ => NormedSpace.exp (u • D)) (fun u : ℝ => NormedSpace.exp (u • -D)) D (-D) hE3 hE2
    (fun u => by simp only [mul_neg, neg_mul, mul_assoc, add_neg_cancel]) (by simp) t
  calc F t = (NormedSpace.exp (t • D) * NormedSpace.exp (t • -D)) * F t := by rw [h2, one_mul]
    _ = NormedSpace.exp (t • D) * (NormedSpace.exp (t • -D) * F t) := by rw [mul_assoc]
    _ = NormedSpace.exp (t • D) := by rw [h1, mul_one]

lemma torep_wt_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (torepSig T) Λ T.w := by
  intro θ _
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin n → ℂ, d = fun b => (θ b : ℂ) * Complex.I := ⟨_, rfl⟩
  have hmem : ∀ t : ℝ, Matrix.diagonal (fun b => Complex.exp (((t * θ b : ℝ) : ℂ) * Complex.I)) ∈ Kset ε :=
    fun t => diag_mem_lemma_3 _ fun b => expI_lemma_4 (t * θ b)
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • Matrix.diagonal d) =
      Matrix.diagonal (fun b => Complex.exp (((t * θ b : ℝ) : ℂ) * Complex.I)) := by
    intro t
    have h1 : (t : ℂ) • Matrix.diagonal d = Matrix.diagonal (fun b => (((t * θ b : ℝ) : ℂ) * Complex.I)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, hd, smul_eq_mul]
        push_cast
        ring
      · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, smul_zero]
    rw [h1, torep_exp_diag]
  have hX : inK ε (Matrix.diagonal d) := torep_inK_diag ε d (fun b => by
    simp only [hd]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring)
  let γ : ℝ → KG ε := fun t => torepK ε (hmem t)
  have hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Matrix.diagonal d) := fun t => by
    rw [hexp t]
    rfl
  have hF := T.hasDeriv _ hX γ hγ
  let F : ℝ → (T.V →L[ℂ] T.V) := fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)
  have hmat : ∀ s t : ℝ, Matrix.diagonal (fun b => Complex.exp ((((s + t) * θ b : ℝ) : ℂ) * Complex.I)) =
      Matrix.diagonal (fun b => Complex.exp (((s * θ b : ℝ) : ℂ) * Complex.I)) *
        Matrix.diagonal (fun b => Complex.exp (((t * θ b : ℝ) : ℂ) * Complex.I)) := by
    intro s t
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext b
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hadd : ∀ s t, F (s + t) = F s * F t := by
    intro s t
    simp only [F, γ]
    rw [torepK_congr_lemma_6 ε (hmem (s + t)) (kset_mul_lemma (hmem s) (hmem t)) (hmat s t),
      torepK_mul_lemma_2 ε (hmem s) (hmem t) (kset_mul_lemma (hmem s) (hmem t)), map_mul]
    try rfl
  have hone : Matrix.diagonal (fun b => Complex.exp ((((0 : ℝ) * θ b : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext b
    simp
  have h0 : F 0 = 1 := by
    simp only [F, γ]
    rw [torepK_congr_lemma_6 ε (hmem 0) (torep_one_mem ε) hone, torepK_one_lemma_7, map_one]
    try rfl
  have hD1 : F 1 = NormedSpace.exp (T.dτ (Matrix.diagonal d)) := by
    rw [oneParam_lemma_5 F _ hadd h0 hF 1, one_smul]
  have hDw : T.dτ (Matrix.diagonal d) T.w = (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by
    rw [torep_diag_sum d, map_sum, ContinuousLinearMap.sum_apply]
    simp only [map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul, hd]
    rw [← Finset.sum_smul]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hm1 : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      Matrix.diagonal (fun b => Complex.exp (((1 * θ b : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    funext b
    rw [one_mul]
  rw [hm1, torepSig_of_mem T (hmem 1)]
  show F 1 T.w = _
  rw [hD1, torep_exp_eigen _ T.w _ hDw, ← Complex.exp_eq_exp_ℂ]

lemma torep_dτ_of_wt {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (torepSig T) μ v) (a : Fin n) :
    T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin n → ℂ, d = fun b => if b = a then Complex.I else 0 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ → Fin n → ℝ, θ = fun t b => if b = a then t else 0 := ⟨_, rfl⟩
  have hmem : ∀ t : ℝ, Matrix.diagonal (fun b => Complex.exp ((θ t b : ℂ) * Complex.I)) ∈ Kset ε :=
    fun t => diag_mem_lemma_3 _ fun b => expI_lemma_4 (θ t b)
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • Matrix.diagonal d) =
      Matrix.diagonal (fun b => Complex.exp ((θ t b : ℂ) * Complex.I)) := by
    intro t
    have h1 : (t : ℂ) • Matrix.diagonal d = Matrix.diagonal (fun b => ((θ t b : ℂ) * Complex.I)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hia : i = a
        · simp [hd, hθ, hia]
        · simp [hd, hθ, hia]
      · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, smul_zero]
    rw [h1, torep_exp_diag]
  have hX : inK ε (Matrix.diagonal d) :=
    torep_inK_diag ε d (fun b => by by_cases hb : b = a <;> simp [hd, hb])
  have hXs : Matrix.diagonal d = Complex.I • Matrix.single a a (1 : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · simp [hd, hia, Matrix.single_apply]
      · simp [hd, hia, Matrix.single_apply, Ne.symm hia]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun h' => hij (h'.1.symm.trans h'.2)), smul_zero]
  let γ : ℝ → KG ε := fun t => torepK ε (hmem t)
  have hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Matrix.diagonal d) := fun t => by
    rw [hexp t]
    rfl
  have hF := T.hasDeriv _ hX γ hγ
  have hF' := ((ContinuousLinearMap.apply ℂ T.V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hF
  have hval : ∀ t : ℝ, ((ContinuousLinearMap.apply ℂ T.V v).restrictScalars ℝ ∘
      fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) t =
      Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • v := by
    intro t
    have h1 := hv (θ t) (hmem t)
    rw [torepSig_of_mem T (hmem t)] at h1
    have h2 : (∑ b, μ b * θ t b : ℝ) = μ a * t := by simp [hθ]
    rw [h2] at h1
    rw [show ((t : ℂ) * ((μ a : ℂ) * Complex.I)) = ((μ a * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact h1
  have hderiv : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • v)
      (((μ a : ℂ) * Complex.I) • v) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)))
        ((μ a : ℂ) * Complex.I) 0 := by
      have h4 := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const ((μ a : ℂ) * Complex.I)).cexp
      simpa using h4
    exact h3.smul_const v
  have hF'' := hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)
  have heq := hF'.unique hF''
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply] at heq
  rw [hXs, map_smul, ContinuousLinearMap.smul_apply, mul_comm, ← smul_smul] at heq
  exact smul_right_injective T.V Complex.I_ne_zero heq

theorem KType.exists_rep {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), (∀ k : KG ε, σ (toMK k) = T.op k) ∧
      Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) σ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ Λ ⊤ := by
  refine ⟨torepSig T, torepSig_toMK T, torep_isURepOn T, ?_⟩
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, ?_,
    ⟨T.w, Submodule.mem_top, ?_, torep_wt_w T⟩, ?_⟩
  · intro S' _ hS'
    exact T.irred S' (fun k v hv => by
      have := hS' (toMK k) k.2 v hv
      rwa [torepSig_toMK] at this)
  · intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · intro μ v _ hv hwt
    obtain ⟨c, hc, he⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.weight_le T hv (torep_dτ_of_wt T hwt)
    exact ⟨c, hc, he⟩

end ReciprocityTheory.ChartRestriction.DS.HW
