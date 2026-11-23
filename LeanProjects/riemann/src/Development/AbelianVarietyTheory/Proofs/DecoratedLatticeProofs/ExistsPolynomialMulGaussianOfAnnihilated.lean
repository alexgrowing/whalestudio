import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqEvalOfDirDerivVanish
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AnnPoly

section Generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dirD (y : E) (g : E → ℂ) : E → ℂ := fun x => deriv (fun t : ℝ => g (x + t • y)) 0

theorem hasDerivAt_line {g : E → ℂ} {x : E} (hg : DifferentiableAt ℝ g x) (y : E) :
    HasDerivAt (fun t : ℝ => g (x + t • y)) (fderiv ℝ g x y) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • y) y 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const y).const_add x
  have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0:ℝ) • y) := by simpa using hg.hasFDerivAt
  exact h2.comp_hasDerivAt 0 h1

theorem dirD_eq {g : E → ℂ} (hg : Differentiable ℝ g) (y : E) : dirD y g = fun x => fderiv ℝ g x y := by
  funext x
  exact (hasDerivAt_line (hg x) y).deriv

theorem contDiff_dirD {g : E → ℂ} (hg : ContDiff ℝ ∞ g) (y : E) : ContDiff ℝ ∞ (dirD y g) := by
  rw [dirD_eq (hg.differentiable (by simp)) y]
  exact ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

theorem foldr_ofFn_dirD {u : E → ℂ} (hu : ContDiff ℝ ∞ u) : ∀ (k : ℕ) (m : Fin k → E),
    (List.ofFn m).foldr dirD u = fun x => iteratedFDeriv ℝ k u x m := by
  intro k
  induction k with
  | zero => intro m; funext x; simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro m
    rw [List.ofFn_succ, List.foldr_cons, ih (fun i => m i.succ)]
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k u) :=
      ContDiff.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top k) hu
    funext x
    have hA : HasFDerivAt (iteratedFDeriv ℝ k u) (fderiv ℝ (iteratedFDeriv ℝ k u) x) (x + (0:ℝ) • m 0) := by
      simpa using (hd x).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => x + t • m 0) (m 0) 0 := by
      simpa using ((hasDerivAt_id' (0:ℝ)).smul_const (m 0)).const_add x
    have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun i => m i.succ)).hasFDerivAt.comp_hasDerivAt 0
      (hA.comp_hasDerivAt 0 hl)
    rw [iteratedFDeriv_succ_apply_left]
    exact h3.deriv

theorem foldr_dirD_eq_zero {T : Type} [Fintype T] [DecidableEq T] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {u : (T → W) → ℂ} (hu : ContDiff ℝ ∞ u) (N : ℕ)
    (h : ∀ L : List (T × W), L.length = N → L.foldr (fun q g => dirD (Pi.single q.1 q.2) g) u = 0) :
    ∀ L : List (T → W), L.length = N → L.foldr dirD u = 0 := by
  intro L hL
  funext x
  rw [← List.ofFn_get L, foldr_ofFn_dirD hu]
  have hs : L.get = fun i => ∑ τ, Pi.single τ (L.get i τ) := funext fun i => (Finset.univ_sum_single (L.get i)).symm
  simp only [Pi.zero_apply]
  rw [hs, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  have e1 : List.ofFn (fun i => (Pi.single (r i) (L.get i (r i)) : T → W)) =
      (List.ofFn fun i => (r i, L.get i (r i))).map (fun q => (Pi.single q.1 q.2 : T → W)) := by
    rw [List.map_ofFn]; rfl
  have h2 := congrFun (h (List.ofFn fun i => (r i, L.get i (r i))) (by simp [hL])) x
  rw [← List.foldr_map, ← e1, foldr_ofFn_dirD hu] at h2
  exact h2

end Generic

section Gauss

open Classical

variable {D : D7} (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gam (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : ℂ := gauss V l s (fun τ => Matrix.of (z τ))

def expo (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : ℂ :=
  -(2 * Real.pi) * ∑ τ, ((|l τ| : ℝ) : ℂ) *
    Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ))

theorem gam_eq (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : gam V l s z = Complex.exp (expo V l s z) := rfl

theorem contDiff_expo : ContDiff ℝ ∞ (expo V l s (n := n)) := by
  unfold expo
  have hst : ContDiff ℝ ∞ (fun w : ℂ => star w) := Complex.conjCLE.contDiff
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag_apply]
  fun_prop

theorem trace_line {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (A B : Matrix (Fin k) (Fin n) ℂ) (t : ℝ) :
    Matrix.trace ((A + t • B)ᴴ * M * (A + t • B)) = Matrix.trace (Aᴴ * M * A) +
      (t : ℂ) * (Matrix.trace (Bᴴ * M * A) + Matrix.trace (Aᴴ * M * B)) + (t : ℂ) ^ 2 * Matrix.trace (Bᴴ * M * B) := by
  have ht : t • B = (t : ℂ) • B := by ext i j; simp [Complex.real_smul]
  rw [ht]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

theorem hasDerivAt_expo (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) (τ : D.what₂.Tau) (X : Fin V.rank → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => expo V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ)))
      (-(2 * Real.pi) * (((|l τ| : ℝ) : ℂ) * (Matrix.trace ((Matrix.of X)ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ)) +
        Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of X)))) 0 := by
  set e : D.what₂.Tau → Fin V.rank → Fin n → ℂ := Pi.single τ X with he
  have hfun : (fun t : ℝ => expo V l s (z + t • e)) = fun t : ℝ => -(2 * Real.pi) * ∑ σ, ((|l σ| : ℝ) : ℂ) *
      (Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
        (t : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) +
        (t : ℂ) ^ 2 * Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) := by
    funext t
    unfold expo
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← trace_line]
    rfl
  rw [hfun]
  refine HasDerivAt.const_mul _ ?_
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp
  have hs : ∀ σ ∈ (Finset.univ : Finset D.what₂.Tau), HasDerivAt (fun t : ℝ => ((|l σ| : ℝ) : ℂ) *
      (Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
        (t : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) +
        (t : ℂ) ^ 2 * Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))))
      (((|l σ| : ℝ) : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ)))) 0 := by
    intro σ _
    set A := Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ))
    set B := Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))
    set C := Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))
    have h := (((hc.mul_const B).const_add A).add ((hc.pow 2).mul_const C)).const_mul (((|l σ| : ℝ) : ℂ))
    exact h.congr_deriv (by simp)
  have hsum := HasDerivAt.fun_sum hs
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single τ]
  · simp [he]
  · intro σ _ hσ; simp [he, Pi.single_eq_of_ne hσ]
  · simp

theorem hasDerivAt_gam (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) (τ : D.what₂.Tau) (X : Fin V.rank → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => gam V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ)))
      (-(linF V l s τ (Matrix.of X) (Matrix.of (z τ))) * gam V l s z) 0 := by
  have h : HasDerivAt (fun t : ℝ => gam V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) _ 0 :=
    (hasDerivAt_expo V l s z τ X).cexp
  refine h.congr_deriv ?_
  have hc : Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of X) =
      conj (Matrix.trace ((Matrix.of X)ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ))) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM τ,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hc, Complex.add_conj, zero_smul, add_zero, ← gam_eq]
  unfold linF
  push_cast
  ring

theorem annC_gam_mul (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    {h : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ} (hh : Differentiable ℝ h) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    annC V l s τ X (fun z => gam V l s z * h z) =
      fun z => gam V l s z * dirD (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) h z := by
  funext z
  have h1 := hasDerivAt_gam V l s hM z τ (fun i j => X i j)
  have h2 := hasDerivAt_line (hh z) (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ)
  show deriv (fun t : ℝ => gam V l s (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ)) *
      h (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) 0 +
      linF V l s τ X (Matrix.of (z τ)) * (gam V l s z * h z) = _
  rw [(h1.fun_mul h2).deriv, dirD_eq hh]
  have hX : Matrix.of (fun i j => X i j) = X := rfl
  simp only [zero_smul, add_zero, hX]
  ring

theorem foldr_annC (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    {u : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ} (hu : ContDiff ℝ ∞ u) :
    ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ),
      ContDiff ℝ ∞ (L.foldr (fun q g => dirD (Pi.single q.1 (fun i j => q.2 i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) g) u) ∧
      L.foldr (fun q g => annC V l s q.1 q.2 g) (fun z => gam V l s z * u z) =
        fun z => gam V l s z *
          L.foldr (fun q g => dirD (Pi.single q.1 (fun i j => q.2 i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) g) u z
  | [] => ⟨hu, rfl⟩
  | q :: L => by
    obtain ⟨h1, h2⟩ := foldr_annC hM hu L
    refine ⟨contDiff_dirD h1 _, ?_⟩
    simp only [List.foldr_cons]
    rw [h2]
    exact annC_gam_mul V l s hM (h1.differentiable (by simp)) q.1 q.2

end Gauss

end GlobalTheory.AnnPoly

namespace GlobalTheory.StdUnn

open GlobalTheory.AnnPoly

theorem exists_poly_mul_gauss_of_annC : ∀ (D : D7) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ), ContDiff ℝ ∞ f → (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annC V l s q.1 q.2 g) f = 0) → ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ z, f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  classical
  intro D V n l s hs N f hf hL
  have hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ := fun τ => (hs τ).2.2.1
  set u : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ := fun z => f z * Complex.exp (-(expo V l s z)) with hu_def
  have hu : ContDiff ℝ ∞ u := hf.mul (contDiff_expo V l s).neg.cexp
  have hfu : (fun z => gam V l s z * u z) = f := by
    funext z
    rw [hu_def, gam_eq, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hU : ∀ L : List (D.what₂.Tau × (Fin V.rank → Fin n → ℂ)), L.length = N →
      L.foldr (fun q g => dirD (Pi.single q.1 q.2) g) u = 0 := by
    intro L hlen
    have h0 := hL (L.map fun q => (q.1, Matrix.of q.2)) (by simp [hlen])
    rw [← hfu, (foldr_annC V l s hM hu _).2, List.foldr_map] at h0
    funext z
    have h := congrFun h0 z
    exact (mul_eq_zero.1 h).resolve_left (Complex.exp_ne_zero _)
  have hall := foldr_dirD_eq_zero hu N hU
  let eL : (D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin V.rank → Fin n → ℂ) :=
    { toFun := fun x τ i j => (x (τ, i, j, false) : ℂ) + (x (τ, i, j, true) : ℂ) * Complex.I
      map_add' := by intro x y; funext τ i j; simp; ring
      map_smul' := by intro c x; funext τ i j; simp; ring }
  have hv : ContDiff ℝ ∞ (u ∘ eL) := hu.comp (LinearMap.toContinuousLinearMap eL).contDiff
  have htr : ∀ L : List (D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ),
      L.foldr dirD (u ∘ eL) = (L.map eL).foldr dirD u ∘ eL := by
    intro L
    induction L with
    | nil => rfl
    | cons y L ih =>
      funext x
      simp only [List.foldr_cons, List.map_cons, ih, dirD, Function.comp, map_add, map_smul]
  obtain ⟨p, hp⟩ := GlobalTheory.PolyOfDeriv.eq_eval_of_dirDeriv_vanish _ N (u ∘ eL) hv (fun L hlen => by
    have h := htr L
    rw [hall (L.map eL) (by simp [hlen])] at h
    exact h)
  let φ : D.what₂.Tau × Fin V.rank × Fin n × Bool → MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ := fun k =>
    if k.2.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ *
        (MvPolynomial.X (k.1, k.2.1, k.2.2.1, false) - MvPolynomial.X (k.1, k.2.1, k.2.2.1, true))
    else MvPolynomial.C (2 : ℂ)⁻¹ *
        (MvPolynomial.X (k.1, k.2.1, k.2.2.1, false) + MvPolynomial.X (k.1, k.2.1, k.2.2.1, true))
  refine ⟨MvPolynomial.bind₁ φ p, fun z => ?_⟩
  let r : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ := fun k =>
    if k.2.2.2 then (z k.1 k.2.1 k.2.2.1).im else (z k.1 k.2.1 k.2.2.1).re
  have her : eL r = z := by
    funext τ i j
    exact Complex.re_add_im (z τ i j)
  have h1 : f z = u z * gam V l s z := by rw [← congrFun hfu z, mul_comm]
  have h2 : u z = MvPolynomial.eval (fun k => (r k : ℂ)) p := by rw [← hp r, Function.comp_apply, her]
  rw [h1, h2]
  congr 1
  unfold evalPoly
  rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
  congr 2
  funext k
  obtain ⟨τ, i, j, b⟩ := k
  cases b
  · simp only [φ, r, Bool.false_eq_true, if_false, if_true, map_mul, map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.of_apply, Algebra.algebraMap_self, RingHom.id_apply, Complex.re_eq_add_conj]
    ring
  · simp only [φ, r, Bool.false_eq_true, if_false, if_true, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.of_apply, Algebra.algebraMap_self, RingHom.id_apply, Complex.im_eq_sub_conj]
    ring

end GlobalTheory.StdUnn

end
