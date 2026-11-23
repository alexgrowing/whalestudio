import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.TubeDeriv

section Jet

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Jet (f : E → ℂ) (a : ℂ) (d : E → ℂ) : Prop :=
  ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt f D 0 ∧ f 0 = a ∧ ∀ v, D v = d v

theorem Jet.congr {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h1 : ∀ x, g x = f x) (h2 : b = a)
    (h3 : ∀ v, e v = d v) : Jet g b e := by
  obtain ⟨D, hD, h0, hd⟩ := h
  have hg : g = f := funext h1
  subst hg
  exact ⟨D, hD, by rw [h0, h2], fun v => by rw [hd, h3]⟩

theorem Jet.const (a : ℂ) : Jet (fun _ : E => a) a (fun _ => 0) := ⟨0, hasStrictFDerivAt_const a 0, rfl, fun _ => rfl⟩

theorem Jet.clm (L : E →L[ℝ] ℂ) : Jet (fun x => L x) 0 (fun x => L x) := ⟨L, L.hasStrictFDerivAt, by simp, fun _ => rfl⟩

theorem Jet.sub {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h' : Jet g b e) :
    Jet (fun x => f x - g x) (a - b) (fun v => d v - e v) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  obtain ⟨D', hD', h0', hd'⟩ := h'
  exact ⟨D - D', hD.sub hD', by simp [h0, h0'], fun v => by simp [hd, hd']⟩

theorem Jet.mul {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h' : Jet g b e) :
    Jet (fun x => f x * g x) (a * b) (fun v => a * e v + b * d v) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  obtain ⟨D', hD', h0', hd'⟩ := h'
  refine ⟨_, hD.mul hD', by simp [h0, h0'], fun v => ?_⟩
  simp [h0, h0', hd, hd']

theorem Jet.sum {ι : Type} [Fintype ι] {f : ι → E → ℂ} {a : ι → ℂ} {d : ι → E → ℂ}
    (h : ∀ i, Jet (f i) (a i) (d i)) : Jet (fun x => ∑ i, f i x) (∑ i, a i) (fun v => ∑ i, d i v) := by
  choose D hD h0 hd using h
  exact ⟨∑ i, D i, HasStrictFDerivAt.fun_sum fun i _ => hD i, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.conj {f : E → ℂ} {a : ℂ} {d : E → ℂ} (h : Jet f a d) :
    Jet (fun x => conj (f x)) (conj a) (fun v => conj (d v)) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  exact ⟨_, hD.star, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.comp_zero {f : E → ℂ} {a : ℂ} (h : Jet f a fun _ => 0) {g : ℂ → ℂ} (hg : ContDiffAt ℝ 1 g a) :
    Jet (fun x => g (f x)) (g a) (fun _ => 0) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  have hg' : HasStrictFDerivAt g (fderiv ℝ g a) (f 0) := by
    rw [h0]
    exact hg.hasStrictFDerivAt one_ne_zero
  exact ⟨_, hg'.comp 0 hD, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.cexp {f : E → ℂ} {d : E → ℂ} (h : Jet f 0 d) : Jet (fun x => Complex.exp (f x)) 1 d := by
  obtain ⟨D, hD, h0, hd⟩ := h
  exact ⟨_, hD.cexp, by simp [h0], fun v => by simp [h0, hd]⟩

theorem Jet.matExp [FiniteDimensional ℝ E] {k : ℕ} (L : E →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    Jet (fun x => NormedSpace.exp (L x) i j) ((1 : Matrix (Fin k) (Fin k) ℂ) i j) (fun v => L v i j) := by
  let _ : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin k) (Fin k) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : E →L[ℝ] Matrix (Fin k) (Fin k) ℂ := LinearMap.toContinuousLinearMap L
  let P : Matrix (Fin k) (Fin k) ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Fin k → ℂ) i)
  have hE : HasStrictFDerivAt (fun x => NormedSpace.exp (Lc x))
      ((1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ).comp Lc) 0 := by
    have h0 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin k) (Fin k) ℂ → _)
        (1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ) (Lc 0) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    exact h0.comp 0 Lc.hasStrictFDerivAt
  refine ⟨P.comp ((1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ).comp Lc),
    P.hasStrictFDerivAt.comp 0 hE, ?_, fun v => rfl⟩
  simp [NormedSpace.exp_zero]

theorem Jet.lin [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] ℂ) : Jet (fun x => L x) 0 (fun x => L x) := Jet.congr (Jet.clm (LinearMap.toContinuousLinearMap L)) (fun _ => rfl) rfl (fun _ => rfl)

end Jet

variable {k : ℕ}

def matL (k : ℕ) : Par k →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun x := unrealify (x.1 : EuclideanSpace ℝ _)
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem jet_hv (j : Fin k) : Jet (fun x : Par k => hv x.2.2 j) 0 (fun x => hv x.2.2 j) := by
  have h := Jet.lin (E := Par k)
    { toFun := fun x : Par k => hv x.2.2 j
      map_add' := fun x y => by simp [hv, add_div]
      map_smul' := fun c x => by simp [hv]; ring }
  exact Jet.congr h (fun _ => rfl) rfl (fun _ => rfl)

theorem jet_angle : Jet (fun x : Par k => (x.2.1 : ℂ) * Complex.I) 0 (fun x => (x.2.1 : ℂ) * Complex.I) := by
  have h := Jet.lin (E := Par k)
    { toFun := fun x : Par k => (x.2.1 : ℂ) * Complex.I
      map_add' := fun x y => by simp only [Prod.snd_add, Prod.fst_add, Complex.ofReal_add]; ring
      map_smul' := fun c x => by simp [Complex.real_smul, mul_assoc] }
  exact Jet.congr h (fun _ => rfl) rfl (fun _ => rfl)

theorem jet_prod (i j : Fin k) : Jet (fun x : Par k => conj (hv x.2.2 i) * hv x.2.2 j) 0 (fun _ => 0) := Jet.congr ((jet_hv i).conj.mul (jet_hv j)) (fun _ => rfl) (by simp) (fun _ => by simp)

theorem jet_nsq : Jet (fun x : Par k => (nsq (hv x.2.2) : ℂ)) 0 (fun _ => 0) := by
  refine Jet.congr (Jet.sum fun j => jet_prod (k := k) j j) (fun x => ?_) (by simp) (fun _ => by simp)
  simp only [nsq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem contDiffAt_root (η : ℝ) : ContDiffAt ℝ 1 (fun z : ℂ => Real.sqrt (1 - η * z.re)) 0 := by
  have h1 : ContDiffAt ℝ 1 (fun z : ℂ => 1 - η * z.re) 0 :=
    contDiffAt_const.sub (contDiffAt_const.mul Complex.reCLM.contDiff.contDiffAt)
  exact h1.sqrt (by simp)

theorem jet_dd (η : ℝ) : Jet (fun x : Par k => (dd η (hv x.2.2) : ℂ)) 1 (fun _ => 0) := by
  have hg : ContDiffAt ℝ 1 (fun z : ℂ => ((Real.sqrt (1 - η * z.re) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) (contDiffAt_root η)
  exact Jet.congr ((jet_nsq (k := k)).comp_zero hg) (fun x => by simp [dd]) (by simp) (fun _ => rfl)

theorem jet_coef (η : ℝ) :
    Jet (fun x : Par k => ((η / (1 + dd η (hv x.2.2)) : ℝ) : ℂ)) ((η / 2 : ℝ) : ℂ) (fun _ => 0) := by
  have h1 : ContDiffAt ℝ 1 (fun z : ℂ => η / (1 + Real.sqrt (1 - η * z.re))) 0 :=
    contDiffAt_const.div (contDiffAt_const.add (contDiffAt_root η)) (by norm_num)
  have hg : ContDiffAt ℝ 1 (fun z : ℂ => ((η / (1 + Real.sqrt (1 - η * z.re)) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) h1
  exact Jet.congr ((jet_nsq (k := k)).comp_zero hg) (fun x => by simp [dd]) (by norm_num) (fun _ => rfl)

theorem jet_kap (i j : Fin (k + 1)) :
    Jet (fun x : Par k => kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _)))
        (Complex.exp (x.2.1 * Complex.I)) i j) ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)
      (fun x => kap (unrealify (x.1 : EuclideanSpace ℝ _)) (x.2.1 * Complex.I) i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (Jet.cexp (jet_angle (k := k))) (fun x => by simp [kap, blk])
        (Matrix.one_apply_eq _) (fun v => by simp [kap, blk])
    | cast j =>
      exact Jet.congr (Jet.const 0) (fun x => by simp [kap, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne') (fun v => by simp [kap, blk])
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (Jet.const 0) (fun x => by simp [kap, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne) (fun v => by simp [kap, blk])
    | cast j =>
      exact Jet.congr (Jet.matExp (matL k) i j) (fun x => by simp [kap, blk]; rfl)
        (by simp [Matrix.one_apply]) (fun v => by simp [kap, blk]; rfl)

theorem jet_sec (η : ℝ) (i j : Fin (k + 1)) :
    Jet (fun x : Par k => sec η (hv x.2.2) i j) ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)
      (fun x => blk 0 (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) 0 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (jet_dd (k := k) η) (fun x => by simp [sec, blk])
        (Matrix.one_apply_eq _) (fun v => by simp [blk])
    | cast j =>
      exact Jet.congr (jet_hv j) (fun x => by simp [sec, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne') (fun v => by simp [blk])
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr ((Jet.const (-(η : ℂ))).mul (jet_hv i).conj) (fun x => by simp [sec, blk])
        (by simp [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]) (fun v => by simp [blk])
    | cast j =>
      exact Jet.congr ((Jet.const ((1 : Matrix (Fin k) (Fin k) ℂ) i j)).sub ((jet_coef η).mul (jet_prod i j)))
        (fun x => by simp [sec, blk]) (by simp [Matrix.one_apply]) (fun v => by simp [blk])

theorem chart_hasStrictFDerivAt (k : ℕ) (η : ℝ) (i j : Fin (k + 1)) :
    ∃ D : Par k →L[ℝ] ℂ, HasStrictFDerivAt (fun x : Par k => chart η x i j) D 0 ∧ ∀ v, D v = tang η v i j := by
  have h : Jet (fun x : Par k => chart η x i j) (∑ l, (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i l * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) l j)
      (fun v => tang η v i j) := by
    refine Jet.congr (Jet.sum fun l => (jet_kap (k := k) i l).mul (jet_sec η l j))
      (fun x => by unfold chart; rw [Matrix.mul_apply]) rfl (fun v => ?_)
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold tang kap blk
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp
  obtain ⟨D, hD, -, hd⟩ := h
  exact ⟨D, hD, hd⟩

end GlobalTheory.TubeDeriv
