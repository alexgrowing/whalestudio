import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviZero

open Filter
open scoped ComplexConjugate

noncomputable section

section Jets

variable {n : ℕ}

def dDir (ξ : Fin n → ℂ) (f : V n → ℂ) (x : V n) : ℂ := ∑ j, wd n j f x * ξ j

def dbDir (ξ : Fin n → ℂ) (f : V n → ℂ) (x : V n) : ℂ := ∑ k, wdb n k f x * conj (ξ k)

theorem wd_congr' {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  simp only [wd, h.fderiv_eq]

theorem leviV_add' {f g : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (ξ : Fin n → ℂ) : leviV n (fun y => f y + g y) x ξ = leviV n f x ξ + leviV n g x ξ := by
  have hev : ∀ k : Fin n, wdb n k (fun y => f y + g y) =ᶠ[𝓝 x]
      fun y => wdb n k f y + wdb n k g y := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
      eventually_differentiableAt_of_contDiffAt hg] with y h1 h2
    exact wdb_add h1 h2
  simp only [leviV, wd_congr' (hev _), wd_add (differentiableAt_wdb hf) (differentiableAt_wdb hg),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviV_mul' {f g : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (ξ : Fin n → ℂ) : leviV n (fun y => f y * g y) x ξ =
      f x * leviV n g x ξ + dbDir ξ f x * dDir ξ g x + (dDir ξ f x * dbDir ξ g x +
        leviV n f x ξ * g x) := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
  have hev : ∀ k : Fin n, wdb n k (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => wdb n k f y * g y + f y * wdb n k g y := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
      eventually_differentiableAt_of_contDiffAt hg] with y h1 h2
    exact wdb_mul h1 h2
  have hterm : ∀ j k : Fin n, wd n j (wdb n k (fun y => f y * g y)) x =
      wd n j (wdb n k f) x * g x + wdb n k f x * wd n j g x +
        (wd n j f x * wdb n k g x + f x * wd n j (wdb n k g) x) := by
    intro j k
    rw [wd_congr' (hev k), wd_add (f := fun y => wdb n k f y * g y) (g := fun y => f y * wdb n k g y)
      ((differentiableAt_wdb hf).mul hg1) (hf1.mul (differentiableAt_wdb hg)),
      wd_mul (differentiableAt_wdb hf) hg1, wd_mul hf1 (differentiableAt_wdb hg)]
  rw [mul_comm (dbDir ξ f x)]
  simp only [leviV, hterm, dDir, dbDir, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem leviV_const' (c : ℂ) (x : V n) (ξ : Fin n → ℂ) : leviV n (fun _ => c) x ξ = 0 := by
  have h0 : ∀ k : Fin n, wdb n k (fun _ : V n => c) = fun _ => 0 := fun k => by
    funext y; simp [wdb]
  simp [leviV, h0, wd]

abbrev JetRing : Type := DualNumber (DualNumber ℂ)

def sJ : JetRing := DualNumber.eps

def tJ : JetRing := TrivSqZeroExt.inl DualNumber.eps

def cJ (c : ℂ) : JetRing := TrivSqZeroExt.inl (TrivSqZeroExt.inl c)

theorem sJ_sq : sJ * sJ = 0 := DualNumber.eps_mul_eps

theorem tJ_sq : tJ * tJ = 0 := by
  rw [tJ, TrivSqZeroExt.inl_mul_inl, DualNumber.eps_mul_eps, TrivSqZeroExt.inl_zero]

structure HasJet (ξ : Fin n → ℂ) (x : V n) (f : V n → ℂ) (a : JetRing) : Prop where
  cd : ContDiffAt ℝ 2 f x
  val : f x = a.fst.fst
  hol : dDir ξ f x = a.snd.fst
  anti : dbDir ξ f x = a.fst.snd
  lev : leviV n f x ξ = a.snd.snd

variable {ξ : Fin n → ℂ} {x : V n}

theorem HasJet.const (c : ℂ) : HasJet ξ x (fun _ => c) (cJ c) :=
  ⟨contDiffAt_const, by simp [cJ], by simp [cJ, dDir, wd], by simp [cJ, dbDir, wdb],
    by simp [cJ, leviV_const']⟩

theorem HasJet.add {f g : V n → ℂ} {a b : JetRing} (hf : HasJet ξ x f a) (hg : HasJet ξ x g b) :
    HasJet ξ x (fun y => f y + g y) (a + b) := by
  have hf1 : DifferentiableAt ℝ f x := hf.cd.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.cd.differentiableAt (by simp)
  refine ⟨hf.cd.add hg.cd, by simp [hf.val, hg.val], ?_, ?_, ?_⟩
  · simp [← hf.hol, ← hg.hol, dDir, wd_add hf1 hg1, add_mul, Finset.sum_add_distrib]
  · simp [← hf.anti, ← hg.anti, dbDir, wdb_add hf1 hg1, add_mul, Finset.sum_add_distrib]
  · simp [← hf.lev, ← hg.lev, leviV_add' hf.cd hg.cd]

theorem HasJet.mul {f g : V n → ℂ} {a b : JetRing} (hf : HasJet ξ x f a) (hg : HasJet ξ x g b) :
    HasJet ξ x (fun y => f y * g y) (a * b) := by
  have hf1 : DifferentiableAt ℝ f x := hf.cd.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.cd.differentiableAt (by simp)
  refine ⟨hf.cd.mul hg.cd, by simp [hf.val, hg.val], ?_, ?_, ?_⟩
  · have : dDir ξ (fun y => f y * g y) x = f x * dDir ξ g x + dDir ξ f x * g x := by
      simp only [dDir, wd_mul hf1 hg1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hf.val, hg.val, hf.hol, hg.hol]
    simp [DualNumber.snd_mul]
  · have : dbDir ξ (fun y => f y * g y) x = f x * dbDir ξ g x + dbDir ξ f x * g x := by
      simp only [dbDir, wdb_mul hf1 hg1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hf.val, hg.val, hf.anti, hg.anti]
    simp [DualNumber.snd_mul]
  · rw [leviV_mul' hf.cd hg.cd, hf.val, hg.val, hf.anti, hg.anti, hf.hol, hg.hol, hf.lev, hg.lev]
    simp [DualNumber.snd_mul]

theorem HasJet.sum {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ} {a : ι → JetRing}
    (h : ∀ i ∈ s, HasJet ξ x (f i) (a i)) : HasJet ξ x (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [cJ] using HasJet.const (ξ := ξ) (x := x) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HasJet.prod {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ} {a : ι → JetRing}
    (h : ∀ i ∈ s, HasJet ξ x (f i) (a i)) : HasJet ξ x (fun y => ∏ i ∈ s, f i y) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [cJ] using HasJet.const (ξ := ξ) (x := x) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HasJet.det {m : ℕ} {M : V n → Matrix (Fin m) (Fin m) ℂ} {A : Matrix (Fin m) (Fin m) JetRing}
    (h : ∀ a b, HasJet ξ x (fun y => M y a b) (A a b)) : HasJet ξ x (fun y => (M y).det) A.det := by
  simp only [Matrix.det_apply']
  refine HasJet.sum _ fun σ _ => HasJet.mul ?_ (HasJet.prod _ fun i _ => h _ _)
  have := HasJet.const (ξ := ξ) (x := x) (((Equiv.Perm.sign σ : ℤ) : ℂ))
  simpa [cJ] using this

theorem coord_diff (m : Fin n) : Differentiable ℂ (fun z : V n => z m) :=
  (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).differentiable

theorem wd_coord (m j : Fin n) (y : V n) : wd n j (fun z : V n => z m) y = if m = j then 1 else 0 := by
  rw [wd_of_differentiableAt (coord_diff m y)]
  have : fderiv ℂ (fun z : V n => z m) y = (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ) :=
    (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).fderiv
  rw [this]
  simp [bas, Pi.single_apply]

theorem coord_cd (m : Fin n) : ContDiff ℝ 2 (fun z : V n => z m) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).contDiff (n := 2)).restrict_scalars ℝ

theorem HasJet.coord (m : Fin n) : HasJet ξ 0 (fun z : V n => z m) (sJ * cJ (ξ m)) := by
  have h0 : ∀ k, wdb n k (fun z : V n => z m) = fun _ => 0 := fun k =>
    funext fun y => wdb_of_differentiableAt (coord_diff m y)
  refine ⟨(coord_cd m).contDiffAt, by simp [sJ], ?_, ?_, ?_⟩
  · simp [dDir, wd_coord, sJ, cJ, DualNumber.snd_mul]
  · simp [dbDir, h0, sJ, cJ, DualNumber.snd_mul]
  · simp [leviV, h0, wd, sJ, cJ, DualNumber.snd_mul]

theorem HasJet.conj_coord (m : Fin n) :
    HasJet ξ 0 (fun z : V n => conj (z m)) (tJ * cJ (conj (ξ m))) := by
  have hd : ∀ y, DifferentiableAt ℝ (fun z : V n => z m) y := fun y =>
    (coord_diff m y).restrictScalars ℝ
  have h0 : ∀ k, wdb n k (fun z : V n => conj (z m)) = fun _ => if m = k then 1 else 0 := fun k =>
    funext fun y => by rw [wdb_conj (hd y), wd_coord]; split_ifs <;> simp
  refine ⟨(Complex.conjCLE.contDiff.comp (coord_cd m)).contDiffAt, by simp [tJ], ?_, ?_, ?_⟩
  · simp [dDir, wd_conj (hd _), wdb_of_differentiableAt (coord_diff m _), tJ, cJ,
      DualNumber.snd_mul]
  · simp [dbDir, h0, tJ, cJ, DualNumber.snd_mul]
  · simp [leviV, h0, wd, tJ, cJ, DualNumber.snd_mul]

end Jets

section Alg

variable {A : Type*} [CommRing A]

theorem det_jet_sq {m : ℕ} {s t : A} (hs : s * s = 0) (ht : t * t = 0) (ε : Fin m → A)
    (hε : ∀ a, ε a * ε a = 1) (Z Z' R : Matrix (Fin m) (Fin m) A)
    (hZ : ∀ a b, a ≤ b → Z a b = 0) (hZ' : ∀ a b, a ≤ b → Z' a b = 0) :
    (Matrix.diagonal ε + s • (Zᵀ * Matrix.diagonal ε) + t • (Matrix.diagonal ε * Z') +
      (s * t) • R).det =
      (∏ a, ε a) * (1 + (∑ b, ε b * (R b b - ∑ a, Z a b * ε a * Z' a b)) * (s * t)) := by
  set D := Matrix.diagonal ε
  have hDD : D * D = 1 := by
    simp [D, Matrix.diagonal_mul_diagonal, hε]
  have huni : ∀ (u : A) (W : Matrix (Fin m) (Fin m) A), (∀ a b, a ≤ b → W a b = 0) →
      (1 + u • W).det = 1 := by
    intro u W hW
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [hW a a le_rfl]
    · intro a b hab
      have hab' : a < b := hab
      simp [hW a b hab'.le, hab'.ne]
  have hfac : D + s • (Zᵀ * D) + t • (D * Z') + (s * t) • R =
      (1 + s • Z)ᵀ * (D * (1 + (s * t) • (D * (R - Zᵀ * D * Z')))) * (1 + t • Z') := by
    have h1 : D * (1 + (s * t) • (D * (R - Zᵀ * D * Z'))) = D + (s * t) • (R - Zᵀ * D * Z') := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    rw [h1]
    set Q := R - Zᵀ * D * Z' with hQ
    have hR : R = Q + Zᵀ * D * Z' := by rw [hQ]; abel
    have e1 : s * (s * t) = 0 := by rw [← mul_assoc, hs, zero_mul]
    have e2 : t * (s * t) = 0 := by rw [mul_left_comm, ht, mul_zero]
    have e4 : s * t * s = 0 := by rw [mul_comm, e1]
    rw [hR]
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_add, e1, e2, e4, mul_zero, zero_smul, add_zero, mul_comm t s]
    abel
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, huni _ _ hZ,
    huni _ _ hZ', Matrix.det_one_add_smul]
  have e3 : (s * t) ^ 2 = 0 := by rw [mul_pow, sq, hs, zero_mul]
  rw [e3, mul_zero, add_zero, one_mul, mul_one, Matrix.det_diagonal]
  congr 3
  simp [D, Matrix.trace, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.diagonal_apply]

end Alg

section Log

variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}

theorem leviV_log_norm {d : V n → ℂ} {e c : ℂ} (he : e * e = 1) (hreal : ∀ y, conj (d y) = d y)
    (hd : HasJet ξ x d (cJ e * (1 + cJ c * (sJ * tJ)))) :
    leviV n (fun y => ((Real.log ‖d y‖ : ℝ) : ℂ)) x ξ = c := by
  have h2 := hd.mul hd
  have hu : (fun y => d y * d y) = fun y => ((Complex.normSq (d y) : ℝ) : ℂ) := by
    funext y; rw [← Complex.mul_conj, hreal]
  rw [hu] at h2
  have hcd : ContDiffAt ℝ 2 (fun y => Complex.normSq (d y)) x := by
    have := Complex.reCLM.contDiff.contDiffAt.comp x h2.cd
    simpa [Function.comp_def] using this
  have hv : Complex.normSq (d x) = 1 := by
    have := h2.val
    simp [cJ, sJ, tJ, he] at this
    exact this
  have hh : dDir ξ (fun y => ((Complex.normSq (d y) : ℝ) : ℂ)) x = 0 := by
    rw [h2.hol]; simp [cJ, sJ, tJ, DualNumber.snd_mul]
  have hl : leviV n (fun y => ((Complex.normSq (d y) : ℝ) : ℂ)) x ξ = 2 * c := by
    rw [h2.lev]; simp [cJ, sJ, tJ, DualNumber.snd_mul]
    linear_combination (2 * c) * he
  have hlog : ContDiffAt ℝ 2 Real.log (Complex.normSq (d x)) := by
    rw [hv]; exact Real.contDiffAt_log.2 one_ne_zero
  have hc := ReciprocityTheory.L2DbarEstimates.leviChain n Real.log (fun v => Complex.normSq (d v)) x ξ hcd hlog
  have hd1 : deriv Real.log (Complex.normSq (d x)) = 1 := by
    rw [Real.deriv_log', hv]; simp
  unfold dDir at hh
  rw [hh, hl, hd1] at hc
  have hf : (fun y => ((Real.log ‖d y‖ : ℝ) : ℂ)) =
      fun y => (((1 / 2 : ℝ) * Real.log (Complex.normSq (d y)) : ℝ) : ℂ) := by
    funext y; rw [IW.log_norm_eq]; congr 1; ring
  rw [hf, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (f := fun y => Real.log (Complex.normSq (d y))) _
    (hcd.log (by rw [hv]; exact one_ne_zero)), hc]
  simp

theorem leviV_sum' {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ}
    (h : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    leviV n (fun y => ∑ i ∈ s, f i y) x ξ = ∑ i ∈ s, leviV n (f i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using leviV_const' 0 x ξ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [leviV_add' (h i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

theorem leviV_const_mul' (c : ℂ) {f : V n → ℂ} (h : ContDiffAt ℝ 2 f x) :
    leviV n (fun y => c * f y) x ξ = c * leviV n f x ξ := by
  rw [leviV_mul' (f := fun _ => c) contDiffAt_const h, leviV_const']
  simp [dDir, dbDir, wd, wdb]

end Log

theorem sum_castLE {M : Type*} [AddCommMonoid M] {m r : ℕ} (h : m ≤ r) (f : Fin r → M) :
    ∑ b : Fin m, f (Fin.castLE h b) = ∑ b : Fin r, if (b : ℕ) < m then f b else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun b _ => Fin.castLE h b) (fun b _ => by simp)
    (fun a _ b _ hab => Fin.castLE_injective h hab) (fun b hb => ?_) (fun _ _ => rfl)
  exact ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def zMat (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) : ℂ :=
  if h : b < a then ξ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), h⟩⟩) else 0

def cH : ℂ →+* JetRing := (TrivSqZeroExt.inlHom _ _).comp (TrivSqZeroExt.inlHom _ _)

theorem cJ_eq (a : ℂ) : cJ a = cH a := rfl

theorem jet_nM (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) :
    HasJet ξ 0 (fun z => ExF.nM X z τ a b) ((if a = b then 1 else 0) + sJ * cH (zMat X ξ τ a b)) := by
  simp only [ExF.nM, mat, nmat, zMat, Matrix.of_apply]
  by_cases h : b < a
  · simp only [dif_pos h, if_neg h.ne', zero_add]
    exact HasJet.coord _
  · simp only [dif_neg h, map_zero, mul_zero, add_zero]
    have := HasJet.const (ξ := ξ) (x := 0) (if a = b then 1 else 0)
    rw [cJ_eq] at this
    split_ifs at this ⊢ <;> simpa using this

theorem jet_conj_nM (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) :
    HasJet ξ 0 (fun z => conj (ExF.nM X z τ a b))
      ((if a = b then 1 else 0) + tJ * cH (conj (zMat X ξ τ a b))) := by
  simp only [ExF.nM, mat, nmat, zMat, Matrix.of_apply]
  by_cases h : b < a
  · simp only [dif_pos h, if_neg h.ne', zero_add]
    exact HasJet.conj_coord _
  · simp only [dif_neg h, map_zero, mul_zero, add_zero]
    have := HasJet.const (ξ := ξ) (x := 0) (if a = b then 1 else 0)
    rw [cJ_eq] at this
    split_ifs at this ⊢ <;> simpa using this

theorem gram_cpt_apply {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) (b c : Fin r) :
    gram τ.1 X.Gm (mat (cpt X x0 z) τ) b c =
      ∑ a, ExF.nM X z τ a b * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (ExF.nM X z τ a c) := by
  have hg : gram τ.1 X.Gm (mat (cpt X x0 z) τ) =
      (ExF.nM X z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
        (ExF.nM X z τ).map (starRingEnd ℂ) := by
    rw [ExF.mat_cpt, FrameDegreeData.gram_mul, ho τ]
  rw [hg, Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

theorem sgn_mul_self (p a : ℕ) : sgn p a * sgn p a = 1 := by
  unfold sgn; split_ifs <;> simp

theorem dmin_cpt_real {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ)
    (i : Fin (r + 1)) : conj (dmin X.Gm (cpt X x0 z) τ i) = dmin X.Gm (cpt X x0 z) τ i := by
  unfold dmin lminor
  rw [RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext b c
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.submatrix_apply, gram_cpt_apply X ho, map_sum, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem leviV_Lm {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (ξ : Fin (nd X) → ℂ) (τ : X.Ψ)
    (i : Fin (r + 1)) :
    leviV (nd X) (fun z => ((IW.Lm X (cpt X x0 z) τ i : ℝ) : ℂ)) 0 ξ =
      ∑ a : Fin r, ∑ b : Fin r, if (b : ℕ) < i ∧ (i : ℕ) ≤ a then
        ((sgn X.p0 a * sgn X.p0 b * ‖zMat X ξ τ a b‖ ^ 2 : ℝ) : ℂ) else 0 := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  set κ : Fin i → Fin r := Fin.castLE hi with hκ
  set ε : Fin r → ℂ := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hε
  have hεε : ∀ a, ε a * ε a = 1 := fun a => by
    simp only [hε]; rw [← Complex.ofReal_mul, sgn_mul_self]; simp
  set Z := zMat X ξ τ with hZ
  have hZ0 : ∀ a b, a ≤ b → Z a b = 0 := fun a b h => by simp [hZ, zMat, not_lt.2 h]
  have hdet := det_jet_sq sJ_sq tJ_sq (fun a : Fin i => cH (ε (κ a)))
    (fun a => by rw [← map_mul, hεε, map_one])
    (Matrix.of fun a b => cH (Z (κ a) (κ b))) (Matrix.of fun a b => cH (conj (Z (κ a) (κ b))))
    (Matrix.of fun b c => ∑ a, cH (Z a (κ b)) * cH (ε a) * cH (conj (Z a (κ c))))
    (fun a b h => by simp [hZ0 (κ a) (κ b) h]) (fun a b h => by simp [hZ0 (κ a) (κ b) h])
  have hjet : HasJet ξ 0 (fun z => dmin X.Gm (cpt X x0 z) τ i) (Matrix.of fun b c => ∑ a,
      ((if a = κ b then 1 else 0) + sJ * cH (Z a (κ b))) * cH (ε a) *
        ((if a = κ c then 1 else 0) + tJ * cH (conj (Z a (κ c))))).det := by
    unfold dmin lminor
    refine HasJet.det fun b c => ?_
    simp only [Matrix.submatrix_apply, gram_cpt_apply X ho, Matrix.of_apply]
    exact HasJet.sum _ fun a _ =>
      ((jet_nM X ξ τ a _).mul (HasJet.const _)).mul (jet_conj_nM X ξ τ a _)
  have hκi : ∀ b c, κ b = κ c ↔ b = c := fun b c => (Fin.castLE_injective hi).eq_iff
  have hmat : (Matrix.of fun b c => ∑ a,
      ((if a = κ b then 1 else 0) + sJ * cH (Z a (κ b))) * cH (ε a) *
        ((if a = κ c then 1 else 0) + tJ * cH (conj (Z a (κ c))))) =
      Matrix.diagonal (fun a : Fin i => cH (ε (κ a))) +
        sJ • ((Matrix.of fun a b => cH (Z (κ a) (κ b)))ᵀ * Matrix.diagonal (fun a : Fin i => cH (ε (κ a)))) +
        tJ • (Matrix.diagonal (fun a : Fin i => cH (ε (κ a))) *
          Matrix.of fun a b => cH (conj (Z (κ a) (κ b)))) +
        (sJ * tJ) • (Matrix.of fun b c => ∑ a, cH (Z a (κ b)) * cH (ε a) * cH (conj (Z a (κ c)))) := by
    ext1 b c
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.diagonal_apply, smul_eq_mul,
      add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, hκi]
    have e1 : ∑ a, sJ * cH (Z a (κ b)) * cH (ε a) * (tJ * cH (conj (Z a (κ c)))) =
        ∑ a, sJ * tJ * (cH (Z a (κ b)) * cH (ε a) * cH (conj (Z a (κ c)))) :=
      Finset.sum_congr rfl fun a _ => by ring
    rw [e1]
    by_cases hbc : b = c
    · subst hbc; simp only [if_true]; ring
    · simp only [if_neg hbc, if_neg (Ne.symm hbc)]; ring
  rw [hmat, hdet] at hjet
  simp only [Matrix.of_apply, ← map_mul, ← map_sum, ← map_sub, ← map_prod] at hjet
  simp only [← cJ_eq] at hjet
  have hee : (∏ a, ε (κ a)) * (∏ a, ε (κ a)) = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun a _ => hεε _
  have := leviV_log_norm hee (fun y => dmin_cpt_real X ho y τ i) hjet
  simp only [IW.Lm]
  rw [this, Finset.sum_comm,
    sum_castLE hi (fun b => ε b * (∑ a, Z a b * ε a * conj (Z a b) -
      ∑ a : Fin i, Z (κ a) b * ε (κ a) * conj (Z (κ a) b)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_castLE hi (fun a => Z a b * ε a * conj (Z a b))]
  by_cases hb : (b : ℕ) < i
  · rw [if_pos hb, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (a : ℕ) < i
    · simp [ha, not_le.2 ha]
    · simp only [if_neg ha, hb, not_lt.1 ha, and_self, if_true, hε]
      push_cast
      rw [← Complex.mul_conj']
      ring
  · simp [hb]

theorem levi_phla_zero (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (ho : IsOrth X x)
    (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
      ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 := by
  have h0 := IW.zero_mem_OmF X x ho
  have hcd : ∀ τ i, ContDiffAt ℝ 2 (fun z => ((IW.Lm X (cpt X x z) τ i : ℝ) : ℂ)) 0 := fun τ i =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      ((IW.Lm_cpt_cdAt X x h0 τ i).of_le HE.two_le_inf)
  have hev : (fun w => ((phla X la (cpt X x w) : ℝ) : ℂ)) =ᶠ[𝓝 0]
      fun w => ∑ τ, ∑ i : Fin r, ((la τ i : ℂ) * ((IW.Lm X (cpt X x w) τ i.succ : ℝ) : ℂ) +
        (-(la τ i : ℂ)) * ((IW.Lm X (cpt X x w) τ i.castSucc : ℝ) : ℂ)) := by
    filter_upwards [IW.phla_cpt_eventually X x h0 la] with w hw
    rw [hw]
    push_cast
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => by ring
  have hc1 : ∀ τ (c : ℂ) i, ContDiffAt ℝ 2 (fun z => c * ((IW.Lm X (cpt X x z) τ i : ℝ) : ℂ)) 0 :=
    fun τ c i => contDiffAt_const.mul (hcd τ i)
  unfold leviM
  rw [leviV_congr hev, leviV_sum' _ fun τ _ => ContDiffAt.sum fun i _ => (hc1 _ _ _).add (hc1 _ _ _),
    Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [leviV_sum' _ fun i _ => (hc1 _ _ _).add (hc1 _ _ _)]
  simp only [leviV_add' (hc1 _ _ _) (hc1 _ _ _), leviV_const_mul' _ (hcd _ _), leviV_Lm X ho]
  set w : Fin r → Fin r → ℝ := fun a b => sgn X.p0 a * sgn X.p0 b * ‖zMat X ξ τ a b‖ ^ 2 with hw
  have hR : ∑ y : {p : Fin r × Fin r // p.2 < p.1}, sgn X.p0 y.1.1 * sgn X.p0 y.1.2 *
      ((la τ y.1.2 : ℝ) - (la τ y.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) (τ, y))‖ ^ 2 =
      ∑ a : Fin r, ∑ b : Fin r, if b < a then ((la τ b : ℝ) - (la τ a : ℝ)) * w a b else 0 := by
    rw [← Fintype.sum_prod_type' (f := fun a b : Fin r =>
      if b < a then ((la τ b : ℝ) - (la τ a : ℝ)) * w a b else 0), ← Finset.sum_filter,
      Finset.sum_subtype (p := fun p : Fin r × Fin r => p.2 < p.1) _ (by simp)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hw, zMat, dif_pos y.2]
    ring
  rw [hR]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hba : b < a
  · have hi : ∀ i : Fin r,
        ((la τ i : ℂ) * (if (b : ℕ) < i.succ ∧ (i.succ : ℕ) ≤ a then ((w a b : ℝ) : ℂ) else 0) +
          (-(la τ i : ℂ)) * (if (b : ℕ) < i.castSucc ∧ (i.castSucc : ℕ) ≤ a then ((w a b : ℝ) : ℂ) else 0)) =
        (if i = b then (la τ i : ℂ) * (w a b : ℝ) else 0) -
          (if i = a then (la τ i : ℂ) * (w a b : ℝ) else 0) := by
      intro i
      have hba' : (b : ℕ) < a := hba
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      split_ifs <;> first | omega | ring
    simp only [hw] at hi
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_sub_distrib, if_pos hba]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← sub_mul, hw]
    norm_cast
  · simp [hba, zMat]

theorem leviZero : (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) :=
  levi_phla_zero

end

end GlobalTheory.LeviZero
