import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitarySmVec

open Filter Topology

section Lin
variable {n : ℕ} {Hm : Mt n}

theorem conjH_left (hH : Hmᴴ = Hm) (hu : IsUnit Hm.det) (Z : Mt n) : (conjH Hm Z)ᴴ * Hm = -(Hm * Z) := by
  rw [conjH, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_nonsing_inv, hH, neg_mul, mul_assoc, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem conjH_right (hu : IsUnit Hm.det) (Z : Mt n) : Hm * conjH Hm Z = -(Zᴴ * Hm) := by
  rw [conjH, mul_neg, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hu, one_mul]

theorem re_mem (hH : Hmᴴ = Hm) (hu : IsUnit Hm.det) (Z : Mt n) : (1 / 2 : ℂ) • (Z + conjH Hm Z) ∈ lieH Hm := by
  show _ * Hm + Hm * _ = 0
  rw [conjTranspose_smul, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, conjH_left hH hu,
    conjH_right hu]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem im_mem (hH : Hmᴴ = Hm) (hu : IsUnit Hm.det) (Z : Mt n) :
    (1 / (2 * Complex.I)) • (Z - conjH Hm Z) ∈ lieH Hm := by
  show _ * Hm + Hm * _ = 0
  rw [conjTranspose_smul, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, conjH_left hH hu,
    conjH_right hu]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [this, neg_smul, sub_neg_eq_add, sub_neg_eq_add, add_comm (Hm * Z), neg_add_cancel]

theorem exp_mem (hu : IsUnit Hm.det) {X : Mt n} (hX : X ∈ lieH Hm) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hu' : IsUnit Hm := (isUnit_iff_isUnit_det Hm).2 hu
  have e : (t • X)ᴴ = Hm * (-(t • X)) * Hm⁻¹ := by
    have h1 : Xᴴ * Hm = -(Hm * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(Hm * X) * Hm⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * Hm * NormedSpace.exp (t • X) = Hm
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ Hm⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem one_mem : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 : Mt n)ᴴ * Hm * 1 = Hm
  simp

theorem mul_mem {a b : Mt n} (ha : a ∈ Formalism.QuantumDeterminants.UH Hm) (hb : b ∈ Formalism.QuantumDeterminants.UH Hm) : a * b ∈ Formalism.QuantumDeterminants.UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

theorem det_unit (hu : IsUnit Hm.det) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) : IsUnit g.det := by
  have h : (gᴴ * Hm * g).det = Hm.det := congrArg det hg
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_right (h ▸ hu)

theorem lie_conj (hu : IsUnit Hm.det) {X g : Mt n} (hX : X ∈ lieH Hm) (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) :
    g⁻¹ * X * g ∈ lieH Hm := by
  have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (det_unit hu hg)
  have hU : gᴴ * Hm * g = Hm := hg
  have hL : Xᴴ * Hm + Hm * X = 0 := hX
  have A : (g⁻¹)ᴴ * Hm = Hm * g := by
    calc (g⁻¹)ᴴ * Hm = (g⁻¹)ᴴ * (gᴴ * Hm * g) := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hm * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hm * g := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hm * g⁻¹ = gᴴ * Hm := by
    calc Hm * g⁻¹ = gᴴ * Hm * g * g⁻¹ := by rw [hU]
      _ = gᴴ * Hm := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  show (g⁻¹ * X * g)ᴴ * Hm + Hm * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hm + Hm * (g⁻¹ * X * g)
        = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * Hm)) + (Hm * g⁻¹) * X * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (Xᴴ * Hm + Hm * X) * g := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hL]; simp

def pr {k : ℕ} (Xs : Fin k → Mt n) (t : Fin k → ℝ) : Mt n := (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod

theorem pr_zero (Xs : Fin 0 → Mt n) (t : Fin 0 → ℝ) : pr Xs t = 1 := by simp [pr]

theorem pr_succ {k : ℕ} (Xs : Fin (k + 1) → Mt n) (t : Fin (k + 1) → ℝ) :
    pr Xs t = pr (Fin.init Xs) (Fin.init t) * NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)) := by
  simp only [pr]
  rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton]
  rfl

theorem pr_mem (hu : IsUnit Hm.det) : ∀ {k : ℕ} (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH Hm) → ∀ t,
    pr Xs t ∈ Formalism.QuantumDeterminants.UH Hm
  | 0, Xs, _, t => by rw [pr_zero]; exact one_mem
  | k + 1, Xs, h, t => by
    rw [pr_succ]
    exact mul_mem (pr_mem hu _ (fun i => h _) _) (exp_mem hu (h _) _)

theorem pr_conj {g : Mt n} (hg : IsUnit g.det) : ∀ {k : ℕ} (Xs : Fin k → Mt n) (t : Fin k → ℝ),
    pr Xs t * g = g * pr (fun i => g⁻¹ * Xs i * g) t
  | 0, Xs, t => by rw [pr_zero, pr_zero, mul_one, one_mul]
  | k + 1, Xs, t => by
    have e : ∀ (s : ℝ) (X : Mt n), NormedSpace.exp (s • X) * g = g * NormedSpace.exp (s • (g⁻¹ * X * g)) := by
      intro s X
      have e1 : s • X = g * (s • (g⁻¹ * X * g)) * g⁻¹ := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        calc X = (g * g⁻¹) * X * (g * g⁻¹) := by rw [mul_nonsing_inv _ hg, one_mul, mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      rw [e1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det g).2 hg), mul_assoc _ g⁻¹, nonsing_inv_mul _ hg, mul_one]
    rw [pr_succ, pr_succ, mul_assoc, e, ← mul_assoc, pr_conj hg, mul_assoc]
    rfl

end Lin

section Fam

variable {n : ℕ} {Hm : Mt n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mt n → (H →L[ℂ] H)}
  {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def SmFam (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (c : E → H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH Hm) →
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × E => σ (pr Xs p.1) (c p.2)

theorem SmFam.const {v : H} (hv : SmoothVec (lieH Hm) σ v) : SmFam Hm σ (fun _ : E => v) :=
  fun k Xs h => (hv k Xs h).comp contDiff_fst

theorem SmFam.vec {c : E → H} (hc : SmFam Hm σ c) (e : E) : SmoothVec (lieH Hm) σ (c e) :=
  fun k Xs h => (hc k Xs h).comp (contDiff_id.prodMk (contDiff_const (c := e)))

theorem SmFam.comp {c : E → H} (hc : SmFam Hm σ c) {φ : F → E} (hφ : ContDiff ℝ ∞ φ) : SmFam Hm σ (fun x => c (φ x)) :=
  fun k Xs h => (hc k Xs h).comp (contDiff_fst.prodMk (hφ.comp contDiff_snd))

theorem SmFam.contDiff (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : E → H} (hc : SmFam Hm σ c) : ContDiff ℝ ∞ c := by
  have h := (hc 0 (fun i => i.elim0) (fun i => i.elim0)).comp
    ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk contDiff_id)
  simpa only [Function.comp_def, pr_zero, hσ.1.1, ContinuousLinearMap.one_apply, id] using h

theorem SmFam.hasDerivAt (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : ℝ → H} (hc : SmFam Hm σ c) :
    HasDerivAt c (deriv c 0) 0 :=
  (((hc.contDiff hσ).differentiable (by simp)) 0).hasDerivAt

theorem SmFam.deriv (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : E × ℝ → H} (hc : SmFam Hm σ c) :
    SmFam Hm σ (fun e => deriv (fun s => c (e, s)) 0) := by
  intro k Xs h
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (p : (Fin k → ℝ) × E) (s : ℝ) => σ (pr Xs p.1) (c (p.2, s))) :=
    (hc k Xs h).comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have h2 := h1.fderiv_apply (n := ∞) (contDiff_const (c := (0 : ℝ))) (contDiff_const (c := (1 : ℝ))) (by simp)
  convert h2 using 2 with p
  have h3 : HasDerivAt (fun s => c (p.2, s)) (_root_.deriv (fun s => c (p.2, s)) 0) 0 :=
    (hc.comp (contDiff_const.prodMk contDiff_id)).hasDerivAt hσ
  have h4 := ((σ (pr Xs p.1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  exact h4.deriv.symm

theorem SmFam.exp (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : E → H} (hc : SmFam Hm σ c) {X : Mt n}
    (hX : X ∈ lieH Hm) : SmFam Hm σ (fun p : E × ℝ => σ (NormedSpace.exp (p.2 • X)) (c p.1)) := by
  intro k Xs h
  have hL : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → Mt n) i ∈ lieH Hm := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using h j
  have hφ : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × E × ℝ => ((Fin.snoc p.1 p.2.2 : Fin (k + 1) → ℝ), p.2.1) := by
    refine ContDiff.prodMk (contDiff_pi.2 fun i => ?_) contDiff_snd.fst
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd.snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  convert (hc (k + 1) _ hL).comp hφ using 2 with p
  simp only [Function.comp, pr_succ, Fin.init_snoc, Fin.snoc_last]
  rw [hσ.1.2 _ (pr_mem hu _ h _) _ (exp_mem hu hX _)]
  rfl

theorem SmFam.dRep (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : E → H} (hc : SmFam Hm σ c) {X : Mt n}
    (hX : X ∈ lieH Hm) : SmFam Hm σ (fun e => dRep σ X (c e)) :=
  (hc.exp hu hσ hX).deriv hσ

theorem SmFam.deriv_vec (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : ℝ → H} (hc : SmFam Hm σ c) :
    SmoothVec (lieH Hm) σ (_root_.deriv c 0) :=
  ((hc.comp (contDiff_snd (E := ℝ))).deriv hσ).vec 0

theorem smFam_orbit (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v : H} (hv : SmoothVec (lieH Hm) σ v)
    {X : Mt n} (hX : X ∈ lieH Hm) : SmFam Hm σ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) :=
  ((SmFam.const (E := ℝ) hv).exp hu hσ hX).comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)

theorem smooth_zero : SmoothVec (lieH Hm) σ 0 := fun k Xs _ => by simpa only [map_zero] using contDiff_const

theorem smooth_add {v w : H} (hv : SmoothVec (lieH Hm) σ v) (hw : SmoothVec (lieH Hm) σ w) :
    SmoothVec (lieH Hm) σ (v + w) := fun k Xs h => by simpa only [map_add] using (hv k Xs h).add (hw k Xs h)

theorem smooth_smul (a : ℂ) {v : H} (hv : SmoothVec (lieH Hm) σ v) :
    SmoothVec (lieH Hm) σ (a • v) := fun k Xs h => by simpa only [map_smul] using (hv k Xs h).const_smul a

theorem smooth_sub {v w : H} (hv : SmoothVec (lieH Hm) σ v) (hw : SmoothVec (lieH Hm) σ w) :
    SmoothVec (lieH Hm) σ (v - w) := fun k Xs h => by simpa only [map_sub] using (hv k Xs h).sub (hw k Xs h)

theorem smooth_span {v : H} (hv : v ∈ Submodule.span ℂ {w | SmoothVec (lieH Hm) σ w}) : SmoothVec (lieH Hm) σ v := by
  induction hv using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact smooth_zero
  | add x y _ _ hx hy => exact smooth_add hx hy
  | smul a x _ hx => exact smooth_smul a hx

theorem smooth_act (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v : H} (hv : SmoothVec (lieH Hm) σ v)
    {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) : SmoothVec (lieH Hm) σ (σ g v) := by
  intro k Xs h
  have h' : ∀ i, g⁻¹ * Xs i * g ∈ lieH Hm := fun i => lie_conj hu (h i) hg
  convert ((σ g).restrictScalars ℝ).contDiff.comp (hv k _ h') using 2 with t
  show (σ (pr Xs t) ∘L σ g) v = (σ g ∘L σ (pr (fun i => g⁻¹ * Xs i * g) t)) v
  rw [← hσ.1.2 _ (pr_mem hu _ h _) _ hg, ← hσ.1.2 _ hg _ (pr_mem hu _ h' _), pr_conj (det_unit hu hg)]

theorem smooth_dRep (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v : H} (hv : SmoothVec (lieH Hm) σ v)
    {X : Mt n} (hX : X ∈ lieH Hm) : SmoothVec (lieH Hm) σ (dRep σ X v) :=
  (smFam_orbit hu hσ hv hX).deriv_vec hσ

theorem hasDerivAt_dRep (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v : H} (hv : SmoothVec (lieH Hm) σ v)
    {X : Mt n} (hX : X ∈ lieH Hm) : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 :=
  (smFam_orbit hu hσ hv hX).hasDerivAt hσ

theorem dRep_skew (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v w : H} (hv : SmoothVec (lieH Hm) σ v)
    (hw : SmoothVec (lieH Hm) σ w) {X : Mt n} (hX : X ∈ lieH Hm) : ⟪v, dRep σ X w⟫_ℂ = -⟪dRep σ X v, w⟫_ℂ := by
  have h := (hasDerivAt_dRep hu hσ hv hX).inner ℂ (hasDerivAt_dRep hu hσ hw hX)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp (t • X)) v, σ (NormedSpace.exp (t • X)) w⟫_ℂ) = fun _ => ⟪v, w⟫_ℂ := by
    funext t
    exact (LinearMap.norm_map_iff_inner_map_map
      ((σ (NormedSpace.exp (t • X)) : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (hσ.2.1 _ (exp_mem hu hX t)) v w
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem SmFam.deriv_dRep (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : ℝ → H} (hc : SmFam Hm σ c)
    {X : Mt n} (hX : X ∈ lieH Hm) :
    _root_.deriv (fun t => Formalism.L2.Theta.dRep σ X (c t)) 0 = Formalism.L2.Theta.dRep σ X (_root_.deriv c 0) := by
  have hd := hc.dRep hu hσ hX
  have hx := smooth_sub (hd.deriv_vec hσ) (smooth_dRep hu hσ (hc.deriv_vec hσ) hX)
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  generalize hxx : _root_.deriv (fun t => Formalism.L2.Theta.dRep σ X (c t)) 0 -
    Formalism.L2.Theta.dRep σ X (_root_.deriv c 0) = x at hx
  have h1 : HasDerivAt (fun t => ⟪x, Formalism.L2.Theta.dRep σ X (c t)⟫_ℂ)
      ⟪x, _root_.deriv (fun t => Formalism.L2.Theta.dRep σ X (c t)) 0⟫_ℂ 0 :=
    ((innerSL ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd.hasDerivAt hσ)
  have h2 : HasDerivAt (fun t => ⟪Formalism.L2.Theta.dRep σ X x, c t⟫_ℂ) ⟪Formalism.L2.Theta.dRep σ X x, _root_.deriv c 0⟫_ℂ 0 :=
    ((innerSL ℂ (Formalism.L2.Theta.dRep σ X x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc.hasDerivAt hσ)
  simp only [dRep_skew hu hσ hx (hc.vec _) hX] at h1
  have h3 := h1.unique h2.neg
  rw [← dRep_skew hu hσ hx (hc.deriv_vec hσ) hX] at h3
  calc ⟪x, x⟫_ℂ = ⟪x, _ - _⟫_ℂ := by rw [hxx]
    _ = 0 := by rw [inner_sub_right, h3, sub_self]

theorem SmFam.word (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : ℝ → H} (hc : SmFam Hm σ c) :
    ∀ l : List (Mt n), (∀ X ∈ l, X ∈ lieH Hm) → SmFam Hm σ (fun t => l.foldr (Formalism.L2.Theta.dRep σ) (c t)) ∧
      _root_.deriv (fun t => l.foldr (Formalism.L2.Theta.dRep σ) (c t)) 0 = l.foldr (Formalism.L2.Theta.dRep σ) (_root_.deriv c 0)
  | [], _ => ⟨hc, rfl⟩
  | X :: l, h => by
    obtain ⟨h1, h2⟩ := hc.word hu hσ l fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    have hX := h X List.mem_cons_self
    refine ⟨h1.dRep hu hσ hX, ?_⟩
    simp only [List.foldr_cons]
    rw [h1.deriv_dRep hu hσ hX, h2]

theorem smooth_comb (a : ℂ) {x y z : H} (hx : SmoothVec (lieH Hm) σ x) (hy : SmoothVec (lieH Hm) σ y)
    (hz : SmoothVec (lieH Hm) σ z) : SmoothVec (lieH Hm) σ (a • (x - y) - z) :=
  smooth_sub (smooth_smul a (smooth_sub hx hy)) hz

theorem smooth_word (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {v : H} (hv : SmoothVec (lieH Hm) σ v)
    (l : List (Mt n)) (h : ∀ X ∈ l, X ∈ lieH Hm) : SmoothVec (lieH Hm) σ (l.foldr (dRep σ) v) :=
  ((SmFam.const (E := ℝ) hv).word hu hσ l h).1.vec 0

theorem word_comb (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (a : ℂ) {x y z : H}
    (hx : SmoothVec (lieH Hm) σ x) (hy : SmoothVec (lieH Hm) σ y) (hz : SmoothVec (lieH Hm) σ z) :
    ∀ l : List (Mt n), (∀ X ∈ l, X ∈ lieH Hm) →
      l.foldr (dRep σ) (a • (x - y) - z) = a • (l.foldr (dRep σ) x - l.foldr (dRep σ) y) - l.foldr (dRep σ) z
  | [], _ => rfl
  | X :: l, h => by
    have h' : ∀ Y ∈ l, Y ∈ lieH Hm := fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    have hX := h X List.mem_cons_self
    have hd := fun (u : H) (hs : SmoothVec (lieH Hm) σ u) => hasDerivAt_dRep hu hσ (smooth_word hu hσ hs l h') hX
    simp only [List.foldr_cons]
    rw [word_comb hu hσ a hx hy hz l h']
    refine HasDerivAt.deriv ?_
    convert (((hd x hx).sub (hd y hy)).const_smul a).sub (hd z hz) using 1
    funext t
    simp

theorem SmFam.hasDerivAt_form (hu : IsUnit Hm.det) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) {c : ℝ → H} (hc : SmFam Hm σ c)
    {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieH Hm) σ ℓ) : HasDerivAt (fun t => ℓ (c t)) (ℓ (_root_.deriv c 0)) 0 := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  set u : ℝ → H := fun t => (((t - 0)⁻¹ : ℝ) : ℂ) • (c t - c 0) - _root_.deriv c 0 with hudef
  have h1 : Tendsto (fun t => (S.map fun l => ‖l.foldr (Formalism.L2.Theta.dRep σ) (u t)‖).sum) (𝓝[≠] 0)
      (𝓝 (S.map fun _ => (0 : ℝ)).sum) := by
    refine tendsto_list_sum S fun l hl => ?_
    obtain ⟨h2, h3⟩ := hc.word hu hσ l (hS l hl)
    have h4 := h2.hasDerivAt hσ
    rw [h3, hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff] at h4
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    refine h4.congr fun t => ?_
    simp only [hudef]
    rw [word_comb hu hσ _ (hc.vec _) (hc.vec _) (hc.deriv_vec hσ) l (hS l hl), Complex.coe_smul]
    rfl
  have h2 := h1.const_mul C
  simp only [List.map_const', List.sum_replicate, smul_zero, mul_zero] at h2
  have h3 : Tendsto (fun t => ℓ (u t)) (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero_norm (fun t => hb _ (smooth_comb _ (hc.vec _) (hc.vec _) (hc.deriv_vec hσ))) h2
  rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff]
  refine h3.congr fun t => ?_
  simp only [hudef]
  rw [map_sub, map_smul, map_sub, Complex.coe_smul]
  rfl

end Fam

theorem smoothVec_basic : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ v ∈ Submodule.span ℂ {w | SmoothVec (lieH Hm) σ w}, SmoothVec (lieH Hm) σ v) ∧ ∀ v, SmoothVec (lieH Hm) σ v → (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, SmoothVec (lieH Hm) σ (σ g v)) ∧ (∀ X ∈ lieH Hm, SmoothVec (lieH Hm) σ (dRep σ X v) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0) ∧ (∀ Z, SmoothVec (lieH Hm) σ (dRepC Hm σ Z v)) ∧ ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieH Hm) σ ℓ → ∀ X ∈ lieH Hm, HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) (ℓ (dRep σ X v)) 0 := by
  intro n Hm H _ _ _ σ hH hd hσ
  have hu : IsUnit Hm.det := isUnit_iff_ne_zero.2 hd
  exact ⟨fun v hv => smooth_span hv, fun v hv => ⟨fun g hg => smooth_act hu hσ hv hg,
    fun X hX => ⟨smooth_dRep hu hσ hv hX, hasDerivAt_dRep hu hσ hv hX⟩,
    fun Z => smooth_add (smooth_dRep hu hσ hv (re_mem hH hu Z)) (smooth_smul _ (smooth_dRep hu hσ hv (im_mem hH hu Z))),
    fun ℓ hℓ X hX => (smFam_orbit hu hσ hv hX).hasDerivAt_form hu hσ hℓ⟩⟩

end GlobalTheory.UnitarySmVec
