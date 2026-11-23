import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.TorusLaw

variable {n : ℕ}

def cd (x : Mt n) (v : Fin n → ℂ) : Mt n := x * diagonal v * x⁻¹

lemma sgn_sq (q a : ℕ) : (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ)) * (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ)) = 1 := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

private lemma det_diagonal_neg_sgn_ne_zero (q : ℕ) :
    (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  intro h0
  have h1 := sgn_sq q (a : ℕ)
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

lemma units_of_orth {H x : Mt n} {q : ℕ} (h : OrthFr H q x) : IsUnit x.det ∧ IsUnit H.det := by
  have hd := det_diagonal_neg_sgn_ne_zero (n := n) q
  rw [← h.2, det_mul, det_mul] at hd
  refine ⟨isUnit_iff_ne_zero.mpr ?_, isUnit_iff_ne_zero.mpr ?_⟩
  · intro h0
    apply hd
    rw [h0, mul_zero]
  · intro h0
    apply hd
    rw [h0, mul_zero, zero_mul]

lemma cd_mul {x : Mt n} (hx : IsUnit x.det) (v v' : Fin n → ℂ) : cd x v * cd x v' = cd x (v * v') := by
  unfold cd
  have hi : x⁻¹ * x = 1 := nonsing_inv_mul x hx
  rw [show v * v' = fun i => v i * v' i from rfl, ← diagonal_mul_diagonal]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc x⁻¹ x, hi, Matrix.one_mul]

lemma cd_one {x : Mt n} (hx : IsUnit x.det) : cd x (fun _ => 1) = 1 := by
  unfold cd
  rw [diagonal_one, Matrix.mul_one, mul_nonsing_inv x hx]

lemma cd_smul (x : Mt n) (c : ℂ) (v : Fin n → ℂ) : c • cd x v = cd x (c • v) := by
  unfold cd
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma cd_neg (x : Mt n) (v : Fin n → ℂ) : cd x (-v) = -cd x v := by
  unfold cd
  rw [show -v = fun i => -v i from rfl, ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]

lemma cd_adj {H x : Mt n} {q : ℕ} (h : OrthFr H q x) (v : Fin n → ℂ) :
    (cd x v)ᴴ * H = H * cd x (star v) := by
  have hx : IsUnit x.det := (units_of_orth h).1
  have e : (x⁻¹)ᴴ * (xᴴ * H * x) * x⁻¹ =
      (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹ := by
    rw [h.2]
  have hH : H = (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹ := by
    rw [← e]
    have h1 : (x⁻¹)ᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv x hx, conjTranspose_one]
    have h2 : x * x⁻¹ = 1 := mul_nonsing_inv x hx
    calc H = ((x⁻¹)ᴴ * xᴴ) * H * (x * x⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (x⁻¹)ᴴ * (xᴴ * H * x) * x⁻¹ := by simp only [Matrix.mul_assoc]
  have e1 : ∀ Z : Mt n, xᴴ * ((x⁻¹)ᴴ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, nonsing_inv_mul x hx, conjTranspose_one, Matrix.one_mul]
  have e2 : ∀ Z : Mt n, x⁻¹ * (x * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, nonsing_inv_mul x hx, Matrix.one_mul]
  rw [hH]
  unfold cd
  simp only [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, e1, e2]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

lemma exp_cd {x : Mt n} (hx : IsUnit x.det) (v : Fin n → ℂ) :
    NormedSpace.exp (cd x v) = cd x (fun a => Complex.exp (v a)) := by
  unfold cd
  rw [Matrix.exp_conj x _ ((Matrix.isUnit_iff_isUnit_det x).mpr hx), Matrix.exp_diagonal, Pi.exp_def]
  simp only [Complex.exp_eq_exp_ℂ]

lemma conjH_cd {H x : Mt n} {q : ℕ} (h : OrthFr H q x) (v : Fin n → ℂ) :
    conjH H (cd x v) = -cd x (star v) := by
  have hH : IsUnit H.det := (units_of_orth h).2
  unfold conjH
  rw [Matrix.mul_assoc, cd_adj h, ← Matrix.mul_assoc, nonsing_inv_mul H hH, Matrix.one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

omit [Fintype ι] [DecidableEq ι] in
lemma torEl_add (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s s' : ι → Fin n → ℝ) :
    torEl x₀ (s + s') = torEl x₀ s * torEl x₀ s' := by
  funext τ
  have hx := (units_of_orth (h τ)).1
  show cd (x₀ τ) (fun a => Complex.exp ((((s + s') τ a : ℝ) : ℂ) * Complex.I)) =
    cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
      cd (x₀ τ) (fun a => Complex.exp (((s' τ a : ℝ) : ℂ) * Complex.I))
  rw [cd_mul hx]
  congr 1
  funext a
  simp only [Pi.add_apply, Pi.mul_apply, Complex.ofReal_add, add_mul, Complex.exp_add]

omit [Fintype ι] [DecidableEq ι] in
lemma torEl_zero (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) : torEl x₀ 0 = 1 := by
  funext τ
  have hx := (units_of_orth (h τ)).1
  show cd (x₀ τ) (fun a => Complex.exp ((((0 : ι → Fin n → ℝ) τ a : ℝ) : ℂ) * Complex.I)) = 1
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  exact cd_one hx

omit [Fintype ι] [DecidableEq ι] in
lemma mul_torEl_mem (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s : ι → Fin n → ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    u * torEl x₀ s ∈ UG Hm := by
  unfold UG
  rw [Set.mem_ofPred_eq]
  intro τ
  have hx := (units_of_orth (h τ)).1
  have ht : (torEl x₀ s τ)ᴴ * Hm τ * torEl x₀ s τ = Hm τ := by
    show (cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)))ᴴ * Hm τ *
      cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = Hm τ
    rw [cd_adj (h τ), Matrix.mul_assoc, cd_mul hx]
    have hs1 : (star fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
        (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = fun _ => 1 := by
      funext a
      show (starRingEnd ℂ) (Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I) = 1
      rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp
    rw [hs1, cd_one hx, Matrix.mul_one]
  have hu' : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  show (u τ * torEl x₀ s τ)ᴴ * Hm τ * (u τ * torEl x₀ s τ) = Hm τ
  rw [conjTranspose_mul]
  calc _ = (torEl x₀ s τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * torEl x₀ s τ := by simp only [Matrix.mul_assoc]
    _ = Hm τ := by rw [hu', ht]

omit [DecidableEq ι] in
lemma torCh_add (s s' : ι → Fin n → ℝ) : torCh w (s + s') = torCh w s * torCh w s' := by
  unfold torCh
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Pi.add_apply, Pi.add_apply, Complex.ofReal_add, add_mul, Complex.exp_add, mul_zpow]

lemma torCh_single (τ : ι) (a : Fin n) (t : ℝ) :
    torCh w (Pi.single τ (Pi.single a t)) = Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) := by
  unfold torCh
  have h1 : ∀ σ ∈ (Finset.univ : Finset ι), σ ≠ τ →
      (∏ b, Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I) ^ w σ b) = 1 := by
    intro σ _ hσ
    simp [Pi.single_eq_of_ne hσ]
  rw [Finset.prod_eq_single τ h1 (fun h => absurd (Finset.mem_univ τ) h)]
  have h2 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ a →
      Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I) ^ w τ b = 1 := by
    intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  rw [Finset.prod_eq_single a h2 (fun h => absurd (Finset.mem_univ a) h)]
  simp only [Pi.single_eq_same]
  rw [← Complex.exp_int_mul]

omit [Fintype ι] in
lemma oneP_eq (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (τ : ι) (a : Fin n) (t : ℝ) :
    (Pi.mulSingle τ (NormedSpace.exp (t • cd (x₀ τ) (Pi.single a (-Complex.I)))) : ι → Mt n) =
      torEl x₀ (Pi.single τ (Pi.single a (-t))) := by
  have hx : IsUnit (x₀ τ).det := (units_of_orth (h τ)).1
  have hsm : t • cd (x₀ τ) (Pi.single a (-Complex.I)) =
      cd (x₀ τ) ((t : ℂ) • Pi.single a (-Complex.I)) := by
    rw [← cd_smul]
    ext i j
    simp [Complex.real_smul]
  rw [hsm, exp_cd hx]
  funext σ
  by_cases hσ : σ = τ
  · rw [hσ, Pi.mulSingle_eq_same]
    show _ = cd (x₀ τ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I))
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Complex.ofReal_neg]
      ring_nf
    · simp [Pi.single_eq_of_ne hb]
  · rw [Pi.mulSingle_eq_of_ne hσ]
    have hxσ : IsUnit (x₀ σ).det := (units_of_orth (h σ)).1
    show (1 : Mt n) = cd (x₀ σ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I))
    simp only [Pi.single_eq_of_ne hσ, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact (cd_one hxσ).symm

private lemma der_zero' (τ : ι) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : der τ (0 : Mt n) f u = 0 := by
  unfold der
  simp [NormedSpace.exp_zero]

lemma law_single (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} (hs : SmFn Hm f) (hk : KilledFn Hm x₀ w f)
    (τ : ι) (a : Fin n) (t : ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    f (u * torEl x₀ (Pi.single τ (Pi.single a t))) = torCh w (Pi.single τ (Pi.single a t)) * f u := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ι → Mt n, S = fun r => torEl x₀ (Pi.single τ (Pi.single a r)) := ⟨_, rfl⟩
  have hS_add : ∀ r r', S (r + r') = S r * S r' := by
    intro r r'
    rw [hSdef]
    simp only [Pi.single_add]
    exact torEl_add h _ _
  have hS0 : S 0 = 1 := by
    rw [hSdef]
    simp only [Pi.single_zero]
    exact torEl_zero h
  have hS_mem : ∀ v ∈ UG Hm, ∀ r, v * S r ∈ UG Hm := by
    intro v hv r
    rw [hSdef]
    exact mul_torEl_mem h _ hv
  obtain ⟨Y, hY⟩ : ∃ Y : Mt n, Y = cd (x₀ τ) (Pi.single a (-Complex.I)) := ⟨_, rfl⟩
  have hexp : ∀ r : ℝ, (Pi.mulSingle τ (NormedSpace.exp (r • Y)) : ι → Mt n) = S (-r) := by
    intro r
    rw [hSdef, hY]
    exact oneP_eq h τ a r
  have hYlie : Y ∈ lieH (Hm τ) := by
    show Yᴴ * Hm τ + Hm τ * Y = 0
    have hst : star (Pi.single a (-Complex.I) : Fin n → ℂ) = -Pi.single a (-Complex.I) := by
      funext b
      by_cases hb : b = a
      · rw [hb]
        simp [Complex.conj_I]
      · simp [Pi.single_eq_of_ne hb]
    rw [hY, cd_adj (h τ), hst, cd_neg, Matrix.mul_neg, neg_add_cancel]
  have hZ : x₀ τ * Matrix.single a a (1 : ℂ) * (x₀ τ)⁻¹ = cd (x₀ τ) (Pi.single a 1) := by
    unfold cd
    rw [Matrix.diagonal_single]
  have hconj : conjH (Hm τ) (cd (x₀ τ) (Pi.single a 1)) = -cd (x₀ τ) (Pi.single a 1) := by
    rw [conjH_cd (h τ)]
    congr 2
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp
    · simp [Pi.single_eq_of_ne hb]
  have hcoef : (1 / (2 * Complex.I)) • (cd (x₀ τ) (Pi.single a 1) - -cd (x₀ τ) (Pi.single a 1)) = Y := by
    have hI : (1 / (2 * Complex.I)) * 2 = -Complex.I := by
      rw [one_div, mul_inv, mul_comm (2 : ℂ)⁻¹, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one, Complex.inv_I]
    rw [sub_neg_eq_add, ← two_smul ℂ, smul_smul, hI, hY, cd_smul]
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp
    · simp [Pi.single_eq_of_ne hb]
  have hd : ∀ v ∈ UG Hm, Complex.I * der τ Y f v = (w τ a : ℂ) * f v := by
    intro v hv
    have hkv := hk τ a a le_rfl v hv
    rw [if_pos rfl, hZ] at hkv
    unfold derC at hkv
    rw [hconj, add_neg_cancel, smul_zero, der_zero', zero_add, hcoef] at hkv
    exact hkv
  have hψ : ∀ v ∈ UG Hm,
      HasDerivAt (fun r : ℝ => f (v * S r)) (Complex.I * (w τ a : ℂ) * f v) 0 := by
    intro v hv
    have hsm := hs 1 (fun _ => τ) (fun _ => Y) (fun _ => hYlie) v hv
    have hneg : (fun r : ℝ => f (v * S (-r))) =
        (fun t : Fin 1 → ℝ => f (v * (List.ofFn fun i =>
          (Pi.mulSingle ((fun _ : Fin 1 => τ) i) (NormedSpace.exp (t i • (fun _ : Fin 1 => Y) i)) : ι → Mt n)).prod)) ∘
          (fun r : ℝ => fun _ : Fin 1 => r) := by
      funext r
      simp [Function.comp, List.ofFn_succ, hexp]
    have hdn : Differentiable ℝ (fun r : ℝ => f (v * S (-r))) := by
      rw [hneg]
      exact (hsm.differentiable (by simp)).comp (differentiable_pi.2 fun _ => differentiable_id)
    have hdiff : Differentiable ℝ (fun r : ℝ => f (v * S r)) := by
      have h3 : (fun r : ℝ => f (v * S r)) = (fun r : ℝ => f (v * S (-r))) ∘ Neg.neg := by
        funext r
        simp only [Function.comp, neg_neg]
      rw [h3]
      exact hdn.comp differentiable_neg
    have hder : deriv (fun r : ℝ => f (v * S r)) 0 = Complex.I * (w τ a : ℂ) * f v := by
      have h1 := hd v hv
      have h2 : der τ Y f v = -deriv (fun r : ℝ => f (v * S r)) 0 := by
        unfold der
        simp only [hexp]
        have h4 := deriv_comp_neg (fun r : ℝ => f (v * S r)) 0
        simp only [neg_zero] at h4
        exact h4
      rw [h2] at h1
      linear_combination Complex.I * h1 + deriv (fun r : ℝ => f (v * S r)) 0 * Complex.I_sq
    rw [← hder]
    exact (hdiff 0).hasDerivAt
  have hφ : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (u * S r)) (Complex.I * (w τ a : ℂ) * f (u * S r)) r := by
    intro r
    have h1 := hψ (u * S r) (hS_mem u hu r)
    have h3 : HasDerivAt (fun x : ℝ => f (u * S r * S (x - r))) (Complex.I * (w τ a : ℂ) * f (u * S r)) r :=
      HasDerivAt.comp_sub_const (f := fun r' : ℝ => f (u * S r * S r')) r r (by rw [sub_self]; exact h1)
    have h2 : (fun x : ℝ => f (u * S r * S (x - r))) = fun x : ℝ => f (u * S x) := by
      funext x
      rw [mul_assoc, ← hS_add, show r + (x - r) = x by ring]
    rw [h2] at h3
    exact h3
  have hg : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) 0 r := by
    intro r
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)))
        (Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * (-(Complex.I * (w τ a : ℂ) * ((1 : ℝ) : ℂ)))) r :=
      (((hasDerivAt_id r).ofReal_comp).const_mul (Complex.I * (w τ a : ℂ))).neg.cexp
    refine (he.mul (hφ r)).congr_deriv ?_
    push_cast
    ring
  have hdg : Differentiable ℝ (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) :=
    fun x => (hg x).differentiableAt
  have hdg' : ∀ x, deriv (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) x = 0 :=
    fun x => (hg x).deriv
  have hgc : Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) * f (u * S t) = f u := by
    refine (is_const_of_deriv_eq_zero hdg hdg' t 0).trans ?_
    simp [hS0]
  have hfin : torEl x₀ (Pi.single τ (Pi.single a t)) = S t := by rw [hSdef]
  rw [hfin, torCh_single]
  have hinv : Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) * Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) = 1 := by
    rw [← Complex.exp_add, show (w τ a : ℂ) * ((t : ℂ) * Complex.I) + -(Complex.I * (w τ a : ℂ) * t) = 0 by ring,
      Complex.exp_zero]
  calc f (u * S t) = Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) *
        (Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) * f (u * S t)) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [hgc]

end GlobalTheory.HolDict.TorusLaw

namespace GlobalTheory.HolDict

open TorusLaw in

theorem torus_law_of_killed : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, SmFn Hm f → KilledFn Hm x₀ w f → ∀ u ∈ UG Hm, ∀ s, f (u * torEl x₀ s) = torCh w s * f u := by
  intro n ι _ _ Hm q x₀ w h f hs hk u hu s
  have key : ∀ S : Finset (ι × Fin n), ∀ v ∈ UG Hm,
      f (v * torEl x₀ (fun τ a => if (τ, a) ∈ S then s τ a else 0)) =
        torCh w (fun τ a => if (τ, a) ∈ S then s τ a else 0) * f v := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v _
      have h0 : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (∅ : Finset (ι × Fin n)) then s τ a else 0) =
          (0 : ι → Fin n → ℝ) := by
        funext τ a
        simp
      have hc0 : torCh w (0 : ι → Fin n → ℝ) = 1 := by
        simp [torCh]
      rw [h0, torEl_zero h, mul_one, hc0, one_mul]
    · intro p S hp ih v hv
      have hps : ∀ (τ : ι) (a : Fin n), (Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) : ι → Fin n → ℝ) τ a =
          if (τ, a) = p then s τ a else 0 := by
        intro τ a
        rcases p with ⟨τ0, a0⟩
        by_cases e1 : τ = τ0 <;> by_cases e2 : a = a0 <;> simp [e1, e2]
      have hsplit : (fun τ a => if (τ, a) ∈ insert p S then s τ a else 0) =
          Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) + (fun τ a => if (τ, a) ∈ S then s τ a else 0) := by
        funext τ a
        rw [Pi.add_apply, Pi.add_apply, hps]
        by_cases e : (τ, a) = p
        · subst e
          simp [hp]
        · simp [e]
      rw [hsplit, torEl_add h, ← mul_assoc, ih _ (mul_torEl_mem h _ hv),
        law_single h hs hk p.1 p.2 (s p.1 p.2) hv, torCh_add]
      ring
  have hfull : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (Finset.univ : Finset (ι × Fin n)) then s τ a else 0) = s := by
    funext τ a
    simp
  have := key Finset.univ u hu
  rwa [hfull] at this

end GlobalTheory.HolDict
