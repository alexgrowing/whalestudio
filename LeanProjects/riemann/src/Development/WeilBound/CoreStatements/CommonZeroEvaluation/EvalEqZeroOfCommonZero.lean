import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.ChowFactor

noncomputable section

variable {n : ℕ}

theorem eval_linForm (x u : Fin n → ℂ) : eval u (linForm x) = ∑ j, u j * x j := by
  simp [linForm, mul_comm]

theorem linForm_isHomogeneous (x : Fin n → ℂ) : (linForm x).IsHomogeneous 1 := by
  unfold linForm
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X (x j) j

theorem eval_single_linForm (x : Fin n → ℂ) (j : Fin n) :
    eval (Pi.single j 1) (linForm x) = x j := by
  rw [eval_linForm]
  simp [Pi.single_apply]

theorem linForm_ne_zero {x : Fin n → ℂ} (hx : x ≠ 0) : linForm x ≠ 0 := by
  intro h
  apply hx
  funext j
  rw [← eval_single_linForm x j, h]
  simp

def shiftHom (x c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (fun j => X j - C (c j) * linForm x)

theorem linForm_dvd_sub_shift (x c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    linForm x ∣ p - shiftHom x c p := by
  have key : (Ideal.Quotient.mkₐ ℂ (Ideal.span {linForm x})).comp (shiftHom x c) =
      Ideal.Quotient.mkₐ ℂ (Ideal.span {linForm x}) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, shiftHom, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-C (c j), by ring⟩
  have h := DFunLike.congr_fun key p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  exact h

theorem eval_shiftHom (x c u : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    eval u (shiftHom x c p) = eval (fun j => u j - c j * ∑ i, u i * x i) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp, map_mul]
    congr 1
    simp [shiftHom, eval_linForm]

theorem shiftHom_eq_zero {x c : Fin n → ℂ} (hc : ∑ j, c j * x j = 1)
    {p : MvPolynomial (Fin n) ℂ} (hp : ∀ u : Fin n → ℂ, ∑ j, u j * x j = 0 → eval u p = 0) :
    shiftHom x c p = 0 := by
  apply MvPolynomial.funext
  intro u
  rw [eval_shiftHom, map_zero]
  apply hp
  have : ∑ j, (u j - c j * ∑ i, u i * x i) * x j =
      ∑ j, u j * x j - (∑ j, c j * x j) * ∑ i, u i * x i := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hc]
  ring

theorem exists_dual {x : Fin n → ℂ} (hx : x ≠ 0) : ∃ c : Fin n → ℂ, ∑ j, c j * x j = 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  refine ⟨Pi.single k (x k)⁻¹, ?_⟩
  have hk' : x k ≠ 0 := hk
  simp [Pi.single_apply, hk']

theorem linForm_dvd_of_vanish {x : Fin n → ℂ} (hx : x ≠ 0) {p : MvPolynomial (Fin n) ℂ}
    (hp : ∀ u : Fin n → ℂ, ∑ j, u j * x j = 0 → eval u p = 0) : linForm x ∣ p := by
  obtain ⟨c, hc⟩ := exists_dual hx
  have := linForm_dvd_sub_shift x c p
  rwa [shiftHom_eq_zero hc hp, sub_zero] at this

theorem linForm_prime {x : Fin n → ℂ} (hx : x ≠ 0) : Prime (linForm x) := by
  obtain ⟨c, hc⟩ := exists_dual hx
  refine ⟨linForm_ne_zero hx, fun hu => ?_, fun a b hab => ?_⟩
  · have h0 := hu.map (eval (0 : Fin n → ℂ))
    rw [eval_linForm] at h0
    simp at h0
  · have hl : shiftHom x c (linForm x) = 0 :=
      shiftHom_eq_zero hc fun u hu => by rw [eval_linForm, hu]
    have h0 : shiftHom x c a * shiftHom x c b = 0 := by
      obtain ⟨r, hr⟩ := hab
      rw [← map_mul, hr, map_mul, hl, zero_mul]
    rcases mul_eq_zero.1 h0 with h | h
    · left
      have := linForm_dvd_sub_shift x c a
      rwa [h, sub_zero] at this
    · right
      have := linForm_dvd_sub_shift x c b
      rwa [h, sub_zero] at this

theorem eq_smul_of_linForm_dvd {x y : Fin n → ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : linForm x ∣ linForm y) : ∃ t : ℂ, y = t • x := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact linForm_ne_zero hy (by simpa using hr)
  have hdeg := congrArg totalDegree hr
  rw [totalDegree_mul_of_isDomain (linForm_ne_zero hx) hr0,
    (linForm_isHomogeneous y).totalDegree (linForm_ne_zero hy),
    (linForm_isHomogeneous x).totalDegree (linForm_ne_zero hx)] at hdeg
  have hr1 : r = C (r.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (by omega)
  refine ⟨r.coeff 0, ?_⟩
  funext j
  have := congrArg (eval (Pi.single j 1)) hr
  rw [hr1, map_mul, eval_single_linForm, eval_single_linForm, eval_C] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [this, mul_comm]

theorem prod_linForm_dvd (P : Finset (Fin n → ℂ)) (h0 : ∀ x ∈ P, x ≠ 0)
    (hprop : ∀ x ∈ P, ∀ x' ∈ P, ∀ t : ℂ, x' = t • x → x' = x)
    {Q : MvPolynomial (Fin n) ℂ} (hQ : ∀ x ∈ P, linForm x ∣ Q) :
    ∏ x ∈ P, linForm x ∣ Q := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 := h0 a (Finset.mem_insert_self a s)
    have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => h0 x (Finset.mem_insert_of_mem hx)
    obtain ⟨R, hR⟩ := ih hs0
      (fun x hx x' hx' t => hprop x (Finset.mem_insert_of_mem hx) x' (Finset.mem_insert_of_mem hx') t)
      (fun x hx => hQ x (Finset.mem_insert_of_mem hx))
    have hp := linForm_prime ha0
    have hdiv : linForm a ∣ (∏ x ∈ s, linForm x) * R := hR ▸ hQ a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    rcases hp.dvd_or_dvd hdiv with h | ⟨R', rfl⟩
    · exfalso
      obtain ⟨y, hy, hdy⟩ := (hp.dvd_finsetProd_iff _).1 h
      obtain ⟨t, ht⟩ := eq_smul_of_linForm_dvd ha0 (hs0 y hy) hdy
      have := hprop a (Finset.mem_insert_self a s) y (Finset.mem_insert_of_mem hy) t ht
      exact ha (this ▸ hy)
    · exact ⟨R', by rw [hR]; ring⟩

variable {e : ℕ}

def firstSub (v : Fin e × Fin n → ℂ) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Fin n) ℂ :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin n) ℂ) (X ij.2) (fun i => C (v (i, ij.2))) ij.1

def sectionPoly (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin e × Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ :=
  aeval (firstSub v) g

theorem eval_sectionPoly (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin e × Fin n → ℂ)
    (u : Fin n → ℂ) : eval u (sectionPoly g v) = eval (consGroup u v) g := by
  unfold sectionPoly
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]
    congr 1
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [firstSub, consGroup]

theorem sectionPoly_isHomogeneous {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ}
    (hg : IsMultiHomog δ g) (v : Fin e × Fin n → ℂ) : (sectionPoly g v).IsHomogeneous δ := by
  classical
  have hs : ∀ ij : Fin (e + 1) × Fin n,
      (firstSub v ij).IsHomogeneous (if ij.1 = 0 then 1 else 0) := by
    rintro ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simpa [firstSub] using isHomogeneous_X ℂ j
    | succ i => simpa [firstSub, Fin.succ_ne_zero] using isHomogeneous_C (Fin n) (v (i, j))
  rw [sectionPoly, aeval_def, eval₂_eq']
  apply IsHomogeneous.sum
  intro d hd
  have hw := congrFun (hg (mem_support_iff.1 hd)) 0
  have h1 : ∑ ij, (if ij.1 = (0 : Fin (e + 1)) then 1 else 0) * d ij = δ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hw
    rw [← hw, Finset.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [groupWeight, Pi.single_apply, eq_comm, mul_comm]
  have hp := IsHomogeneous.prod Finset.univ (fun ij => firstSub v ij ^ d ij) _
    (fun ij _ => (hs ij).pow (d ij))
  rw [h1] at hp
  simpa using (isHomogeneous_C (Fin n) (coeff d g)).mul hp

theorem eval_eq_zero_of_common_zero {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hg : IsChowForm W (e + 1) g)
    {w : Fin (e + 1) × Fin n → ℂ} {x : Fin n → ℂ} (hx : x ≠ 0) (hW : ∀ q ∈ W, eval x q = 0)
    (hw : ∀ i, ∑ j, w (i, j) * x j = 0) : eval w g = 0 := by
  set a := algebraMap ℂ (AlgebraicClosure ℂ) with ha
  have hinj : Function.Injective a := a.injective
  have hmem : (a ∘ w) ∈ incidence W (e + 1) := by
    refine ⟨a ∘ x, fun h => hx ?_, fun q hq => ?_, fun i => ?_⟩
    · funext j
      apply hinj
      simpa using congrFun h j
    · have h1 : aeval x q = 0 := hW q hq
      rw [aeval_algebraMap_apply, h1, map_zero]
    · have := congrArg a (hw i)
      simpa [map_sum] using this
  have h := (hg.2 g).2 dvd_rfl _ hmem
  rw [aeval_algebraMap_apply] at h
  exact hinj (h.trans (map_zero a).symm)

end

end ModelDimension.ChowFactor

open ModelDimension.ChowFactor in

theorem ModelDimension.chow_form_product_formula :
    ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
  (v : Fin e × Fin n → ℂ) (P : Finset (Fin n → ℂ)) (u₀ : Fin n → ℂ),
  IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (∀ x ∈ P, x ≠ 0 ∧ (∀ q ∈ W, eval x q = 0) ∧ ∀ i, ∑ j, v (i, j) * x j = 0) →
  (∀ x ∈ P, ∀ x' ∈ P, ∀ t : ℂ, x' = t • x → x' = x) →
  P.card = δ → eval (consGroup u₀ v) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u v) g = c * ∏ x ∈ P, ∑ j, u j * x j := by
  intro n e δ W g v P u₀ hg hd hP hprop hcard hne
  have hQ0 : sectionPoly g v ≠ 0 := by
    intro h
    apply hne
    rw [← eval_sectionPoly, h, map_zero]
  have hdvd : ∏ x ∈ P, linForm x ∣ sectionPoly g v := by
    refine prod_linForm_dvd P (fun x hx => (hP x hx).1) hprop fun x hx => ?_
    obtain ⟨hx0, hxW, hxv⟩ := hP x hx
    refine linForm_dvd_of_vanish hx0 fun u hu => ?_
    rw [eval_sectionPoly]
    refine eval_eq_zero_of_common_zero hg hx0 hxW fun i => ?_
    cases i using Fin.cases with
    | zero => simpa [consGroup] using hu
    | succ i => simpa [consGroup] using hxv i
  obtain ⟨R, hR⟩ := hdvd
  have hprod0 : ∏ x ∈ P, linForm x ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x hx => linForm_ne_zero (hP x hx).1
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hQ0 (by simpa using hR)
  have hprodH : (∏ x ∈ P, linForm x).IsHomogeneous δ := by
    have := IsHomogeneous.prod P (fun x => linForm x) (fun _ => 1)
      (fun x _ => linForm_isHomogeneous x)
    simpa [hcard] using this
  have hdeg := congrArg totalDegree hR
  rw [totalDegree_mul_of_isDomain hprod0 hR0, hprodH.totalDegree hprod0,
    (sectionPoly_isHomogeneous hd v).totalDegree hQ0] at hdeg
  have hR1 : R = C (R.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (by omega)
  refine ⟨R.coeff 0, ?_, fun u => ?_⟩
  · intro h
    rw [h, map_zero] at hR1
    exact hR0 hR1
  · rw [← eval_sectionPoly, hR, hR1, map_mul, eval_C, map_prod, mul_comm]
    simp only [eval_linForm, coeff_C, if_true]
