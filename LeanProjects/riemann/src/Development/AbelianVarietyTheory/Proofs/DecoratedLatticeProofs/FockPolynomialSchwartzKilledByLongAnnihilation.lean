import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockAnnKill

open MvPolynomial

variable {D : D7}

theorem hasDerivAt_eval_line {σ : Type} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℂ) (v c : σ → ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => eval (v + (t : ℂ) • c) p) (∑ k, c k * eval (v + (t : ℂ) • c) (pderiv k p)) t := by
  have hl : ∀ k, HasDerivAt (fun t : ℝ => (v + (t : ℂ) • c) k) (c k) t := fun k => by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (c k)).const_add (v k)
    simpa [Complex.ofRealCLM_apply] using this
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t (eval (v + (t : ℂ) • c) (C a))
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, eval_X, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, mul_add]
    have h := hp.mul (hl k)
    refine h.congr_deriv ?_
    have hs : ∀ j, eval (v + (t : ℂ) • c) (Pi.single (M := fun _ : σ => MvPolynomial σ ℂ) j 1 k) = if j = k then 1 else 0 := by
      intro j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Pi.single_apply, Ne.symm hj, hj]
    rw [Finset.sum_add_distrib, Finset.sum_mul]
    conv_rhs => rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

section Line

variable (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

open Classical in

def dirAt {m : ℕ} (τ : D.what₂.Tau) (X : Matrix (Fin m) (Fin n) ℂ) : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ :=
  fun τ' => if τ' = τ then X else 0

theorem hasDerivAt_gauss (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gauss V l s (z + (t : ℂ) • dirAt τ X)) (-(linF V l s τ X (z τ)) * gauss V l s z) 0 := by
  set Y := dirAt τ X with hY
  set M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ' => gramAt D V τ' * s τ' with hMdef
  set a : D.what₂.Tau → ℂ := fun τ' => Matrix.trace ((z τ')ᴴ * M τ' * z τ') with ha
  set b : D.what₂.Tau → ℂ := fun τ' => Matrix.trace ((Y τ')ᴴ * M τ' * z τ') + Matrix.trace ((z τ')ᴴ * M τ' * Y τ') with hb
  set d : D.what₂.Tau → ℂ := fun τ' => Matrix.trace ((Y τ')ᴴ * M τ' * Y τ') with hd
  have key : ∀ τ' (t : ℝ), Matrix.trace ((z τ' + (t : ℂ) • Y τ')ᴴ * M τ' * (z τ' + (t : ℂ) • Y τ')) =
      a τ' + (t : ℂ) * b τ' + (t : ℂ) * (t : ℂ) * d τ' := by
    intro τ' t
    simp only [ha, hb, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  have hfun : (fun t : ℝ => gauss V l s (z + (t : ℂ) • Y)) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi) * ∑ τ', ((|l τ'| : ℝ) : ℂ) * (a τ' + (t : ℂ) * b τ' + (t : ℂ) * (t : ℂ) * d τ')) := by
    funext t
    unfold gauss
    congr 2
    refine Finset.sum_congr rfl fun τ' _ => ?_
    rw [← key τ' t]
    rfl
  have ho : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    have := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    simpa using this
  have hterm : ∀ τ' ∈ (Finset.univ : Finset D.what₂.Tau), HasDerivAt
      (fun t : ℝ => ((|l τ'| : ℝ) : ℂ) * (a τ' + (t : ℂ) * b τ' + (t : ℂ) * (t : ℂ) * d τ')) (((|l τ'| : ℝ) : ℂ) * b τ') 0 := by
    intro τ' _
    have h := (((ho.mul_const (b τ')).const_add (a τ')).add ((ho.mul ho).mul_const (d τ'))).const_mul ((|l τ'| : ℝ) : ℂ)
    refine h.congr_deriv ?_
    simp
  have hsum := (HasDerivAt.fun_sum hterm).const_mul (-(2 * Real.pi : ℂ))
  have hexp := hsum.cexp
  have hb0 : ∀ τ' ≠ τ, b τ' = 0 := fun τ' h => by simp [hb, hY, dirAt, h]
  have hsb : ∑ τ', ((|l τ'| : ℝ) : ℂ) * b τ' = ((|l τ| : ℝ) : ℂ) * b τ :=
    Finset.sum_eq_single τ (fun τ' _ h => by rw [hb0 τ' h, mul_zero]) (by simp)
  have hz := congrFun hfun 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_mul, mul_zero] at hz
  rw [hfun]
  refine hexp.congr_deriv ?_
  rw [hsb]
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_zero]
  rw [← hz]
  have hbτ : b τ = ((2 * (Matrix.trace (Xᴴ * (gramAt D V τ * s τ) * z τ)).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj]
    simp only [hb, hY, dirAt, if_true, hMdef]
    congr 1
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (hM τ).eq, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [hbτ]
  unfold linF
  push_cast
  ring

variable {θ : InfFam D}

theorem compAt_add' (τ : D.what₂.Tau) {m : ℕ} (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [(infPart D).map_add, (θ τ).map_add]

theorem compAt_add_lineAt (hθ : IsInfFam θ) {m : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (X : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) = (fun τ' => compAt θ τ' x) + (t : ℂ) • dirAt τ X := by
  funext τ'
  rw [compAt_add', (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ X).2.2 t τ']
  simp only [Pi.add_apply, Pi.smul_apply, dirAt]
  split_ifs <;> simp

theorem finPart_add_lineAt (hθ : IsInfFam θ) {m : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (X : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = fun i j => finPart D (x i j) := by
  funext i j
  have h := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ X).2.1 t) i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at h
  rw [Matrix.add_apply, (finPart D).map_add, h, add_zero]

end Line

section Span

variable {θ : InfFam D} (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def ptOf {m : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : D.what₂.Tau × Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1

theorem evalPoly_eq {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly p z = eval (ptOf z) p := rfl

theorem ptOf_add_smul {m : ℕ} (z Y : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptOf (z + (t : ℂ) • Y) = ptOf z + (t : ℂ) • ptOf Y := by
  funext k
  simp only [ptOf, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

variable (θ) in

def gen (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => evalPoly (monomial e 1) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
    g (fun i j => finPart D (x i j))

variable (θ n) in

def lowDeg (N : ℕ) : Submodule ℂ (Mx D V.rank n → ℂ) :=
  Submodule.span ℂ {φ | ∃ e g, Finsupp.degree e < N ∧ φ = gen θ V l s e g}

open Classical in
theorem hasDerivAt_gen (hθ : IsInfFam θ) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian)
    (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (x : Mx D V.rank n) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gen θ V l s e g (x + lineAt θ τ X t))
      ((∑ k, ptOf (dirAt τ X) k * eval (ptOf (fun τ' => compAt θ τ' x)) (pderiv k (monomial e 1))) *
        gauss V l s (fun τ' => compAt θ τ' x) * g (fun i j => finPart D (x i j)) -
        linF V l s τ X (compAt θ τ x) * gen θ V l s e g x) 0 := by
  have hfun : (fun t : ℝ => gen θ V l s e g (x + lineAt θ τ X t)) = fun t : ℝ =>
      eval (ptOf (fun τ' => compAt θ τ' x) + (t : ℂ) • ptOf (dirAt τ X)) (monomial e 1) *
        gauss V l s ((fun τ' => compAt θ τ' x) + (t : ℂ) • dirAt τ X) * g (fun i j => finPart D (x i j)) := by
    funext t
    simp only [gen]
    rw [compAt_add_lineAt hθ, finPart_add_lineAt hθ, evalPoly_eq, ptOf_add_smul]
  rw [hfun]
  have h := ((hasDerivAt_eval_line (monomial e 1) (ptOf (fun τ' => compAt θ τ' x)) (ptOf (dirAt τ X)) 0).mul
    (hasDerivAt_gauss V l s hM (fun τ' => compAt θ τ' x) τ X)).mul_const (g (fun i j => finPart D (x i j)))
  refine h.congr_deriv ?_
  simp only [gen, evalPoly_eq, Complex.ofReal_zero, zero_smul, add_zero]
  ring

open Classical in
theorem annS_gen (hθ : IsInfFam θ) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian)
    (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    annS V l s θ τ X (gen θ V l s e g) =
      ∑ k, (ptOf (dirAt τ X) k * (e k : ℂ)) • gen θ V l s (e - Finsupp.single k 1) g := by
  funext x
  unfold annS
  rw [(hasDerivAt_gen V l s hθ hM e g x τ X).deriv, sub_add_cancel, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, gen, evalPoly_eq, pderiv_monomial, eval_monomial]
  ring

theorem differentiableAt_of_mem (hθ : IsInfFam θ) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) {N : ℕ}
    {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ lowDeg θ V n l s N) (x : Mx D V.rank n) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) : DifferentiableAt ℝ (fun t : ℝ => φ (x + lineAt θ τ X t)) 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨e, g, -, rfl⟩ := h
    exact (hasDerivAt_gen V l s hθ hM e g x τ X).differentiableAt
  | zero => exact differentiableAt_const _
  | add a b _ _ ha hb => exact ha.add hb
  | smul c a _ ha => exact ha.const_mul c

theorem degree_sub_single_lt {σ : Type} {N : ℕ} (e : σ →₀ ℕ) (k : σ) (he : Finsupp.degree e < N + 1) (hk : e k ≠ 0) :
    Finsupp.degree (e - Finsupp.single k 1) < N := by
  have h1 : Finsupp.single k 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    omega
  have h2 : e = (e - Finsupp.single k 1) + Finsupp.single k 1 := (tsub_add_cancel_of_le h1).symm
  have h3 : Finsupp.degree e = Finsupp.degree (e - Finsupp.single k 1) + 1 := by
    conv_lhs => rw [h2]
    rw [map_add, Finsupp.degree_single]
  omega

theorem annS_mem (hθ : IsInfFam θ) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) {N : ℕ}
    {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ lowDeg θ V n l s (N + 1)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    annS V l s θ τ X φ ∈ lowDeg θ V n l s N := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨e, g, he, rfl⟩ := h
    rw [annS_gen V l s hθ hM]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : e k = 0
    · rw [hk, Nat.cast_zero, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, g, degree_sub_single_lt e k he hk, rfl⟩)
  | zero =>
    have : annS V l s θ τ X (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [annS]
    rw [this]
    exact Submodule.zero_mem _
  | add a b ha' hb' ha hb =>
    have : annS V l s θ τ X (a + b) = annS V l s θ τ X a + annS V l s θ τ X b := by
      funext x
      simp only [annS, Pi.add_apply]
      rw [deriv_fun_add (differentiableAt_of_mem V l s hθ hM ha' x τ X) (differentiableAt_of_mem V l s hθ hM hb' x τ X)]
      ring
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : annS V l s θ τ X (c • a) = c • annS V l s θ τ X a := by
      funext x
      simp only [annS, Pi.smul_apply, smul_eq_mul]
      rw [deriv_const_mul_field']
      ring
    rw [this]
    exact Submodule.smul_mem _ _ ha

theorem lowDeg_mono {N M : ℕ} (h : N ≤ M) : lowDeg θ V n l s N ≤ lowDeg θ V n l s M :=
  Submodule.span_mono fun _ ⟨e, g, he, hφ⟩ => ⟨e, g, lt_of_lt_of_le he h, hφ⟩

theorem lowDeg_zero : lowDeg θ V n l s 0 = ⊥ :=
  Submodule.span_eq_bot.2 fun _ ⟨_, _, he, _⟩ => absurd he (Nat.not_lt_zero _)

theorem exists_lowDeg {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ fockA θ V n l s) : ∃ N, φ ∈ lowDeg θ V n l s N := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨p, g, -, rfl⟩ := h
    refine ⟨p.totalDegree + 1, ?_⟩
    have hsum : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
        g (fun i j => finPart D (x i j))) = ∑ e ∈ p.support, coeff e p • gen θ V l s e g := by
      funext x
      rw [Finset.sum_apply]
      simp only [gen, Pi.smul_apply, smul_eq_mul, evalPoly_eq]
      conv_lhs => rw [p.as_sum]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_monomial, eval_monomial]
      ring
    rw [hsum]
    exact Submodule.sum_mem _ fun e he => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨e, g, Nat.lt_succ_of_le (le_totalDegree he), rfl⟩)
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨M, hM⟩ := hb
    exact ⟨max N M, Submodule.add_mem _ (lowDeg_mono V l s (le_max_left N M) hN) (lowDeg_mono V l s (le_max_right N M) hM)⟩
  | smul c a _ ha =>
    obtain ⟨N, hN⟩ := ha
    exact ⟨N, Submodule.smul_mem _ _ hN⟩

end Span

open scoped ComplexOrder in

theorem fockA_killed_by_annS : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ φ ∈ fockA θ V n l s, ∃ N : ℕ, ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0 := by
  intro D θ hθ V n l s hs φ hφ
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hs τ).2.2.isHermitian
  obtain ⟨N, hN⟩ := exists_lowDeg V l s hφ
  have key : ∀ (L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ)) (M : ℕ), φ ∈ lowDeg θ V n l s (L.length + M) →
      L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ ∈ lowDeg θ V n l s M := by
    intro L
    induction L with
    | nil => intro M h; simpa using h
    | cons q L ih =>
      intro M h
      rw [List.foldr_cons]
      refine annS_mem V l s hθ hM (ih (M + 1) ?_) q.1 q.2
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1 M] using h
  refine ⟨N, fun L hL => ?_⟩
  have h := key L 0 (by rw [hL, Nat.add_zero]; exact hN)
  rw [lowDeg_zero] at h
  exact (Submodule.mem_bot ℂ).1 h

end GlobalTheory.FockAnnKill

end
