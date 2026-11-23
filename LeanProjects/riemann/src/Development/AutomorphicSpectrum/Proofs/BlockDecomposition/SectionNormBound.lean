import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByPartsStatement

noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.SecBd

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem basis_true_eq_single (a c : Fin n) : bs (true, a, c) = Matrix.single a c (1 : ℂ) := by simp [bs]

theorem bs_f (a c : Fin n) : bs (false, a, c) = Matrix.single a c Complex.I := by simp [bs]

theorem Rw_append {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × Fin n × Fin n))
    (p : Bool × Fin n × Fin n) (f : Mat n → V) : Rw (w ++ [p]) f = Rw w (Rd (bs p) f) := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    show Rd (bs q) (Rw (w ++ [p]) f) = Rd (bs q) (Rw w (Rd (bs p) f))
    rw [ih]

theorem Rd_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X - X') f g = Rd X f g - Rd X' f g := by
  simp [Rd, mul_sub]

theorem Rd_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X + X') f g = Rd X f g + Rd X' f g := by
  simp [Rd, mul_add]

theorem single_conj (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]

theorem skewY (a c : Fin n) :
    (Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ) : Mat n)ᴴ = -(Matrix.single a c (1 : ℂ) - Matrix.single c a 1) := by
  simp [Matrix.conjTranspose_sub, single_conj]

theorem skewZ (a c : Fin n) :
    (Matrix.single a c Complex.I + Matrix.single c a Complex.I : Mat n)ᴴ =
      -(Matrix.single a c Complex.I + Matrix.single c a Complex.I) := by
  simp [Matrix.conjTranspose_add, single_conj, Matrix.single_neg, add_comm]

section L2

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem cls_eq {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = h.toLp _ := dif_pos h

theorem cls_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f =ᵐ[μ] fun y => f y.val := by
  rw [cls_eq μ h]
  exact h.coeFn_toLp

theorem cls_congr {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (e : ∀ g ∈ GLs n, f g = f' g) :
    cls μ f = cls μ f' := by
  have e' : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => e _ (val_mem y)
  have h' : MemLp (fun y : G n => f' y.val) 2 μ := e' ▸ h
  rw [cls_eq μ h, cls_eq μ h']
  exact MemLp.toLp_congr h h' (by rw [e'])

theorem cls_sub {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (h' : MemLp (fun y : G n => f' y.val) 2 μ) :
    cls μ (fun g => f g - f' g) = cls μ f - cls μ f' := by
  rw [cls_eq μ h, cls_eq μ h', cls_eq μ (h.sub h')]
  exact MemLp.toLp_sub h h'

theorem cls_sum {ι : Type} (s : Finset ι) (F : ι → Mat n → V)
    (h : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ) :
    MemLp (fun y : G n => ∑ i ∈ s, F i y.val) 2 μ ∧ cls μ (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, cls μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : MemLp (fun _ : G n => (0 : V)) 2 μ := MemLp.zero
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    rw [cls_eq μ h0]
    exact MemLp.toLp_zero h0
  | insert i s hi ih =>
    obtain ⟨m, e⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hi' := h i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    refine ⟨hi'.add m, ?_⟩
    rw [← e, cls_eq μ hi', cls_eq μ (f := fun g => ∑ i ∈ s, F i g) m,
      cls_eq μ (f := fun g => F i g + ∑ i ∈ s, F i g) (hi'.add m)]
    exact MemLp.toLp_add hi' m

theorem norm_le_of_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (x : Lp V 2 μ) (C : V →L[ℂ] V)
    (e : ∀ᵐ y ∂μ, x y = C (f (y : G n).val)) : ‖x‖ ≤ ‖C‖ * ‖cls μ f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [e, cls_ae μ h] with y h1 h2
  rw [h1, h2]
  exact C.le_opNorm _

end L2

theorem pol_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    -(⟪v, u⟫_ℂ).re ≤ ‖u - v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u + v‖]

theorem pol_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    (⟪v, u⟫_ℂ).re ≤ ‖u + v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u - v‖]

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Rd (hR : RCalc) {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) : Sob μ (Rd (bs p) f) :=
  ⟨((hR n).1 V f hS.1).1 _, fun w => by
    have := hS.2 (w ++ [p])
    rwa [Rw_append] at this⟩

theorem mem1 {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) :
    MemLp (fun y : G n => Rd (bs p) f y.val) 2 μ := hS.2 [p]

theorem mem0 {f : Mat n → V} (hS : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hS.2 []

end Main

theorem secBound (hI : IbpSob) : SecBound := by
  intro n _ _ μ _ E hL hU hR
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewZ a c)
  refine ⟨∑ a, ∑ c, (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4, fun f hS hsec => ?_⟩
  have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
  set x := cls μ f with hx
  have hf0 := mem0 μ hS

  have hd : ∀ p q : Bool × Fin n × Fin n, MemLp (fun y : G n => Rd (bs p) (Rd (bs q) f) y.val) 2 μ := fun p q =>
    mem1 μ (sob_Rd μ hR hS q) p
  have hip : ∀ p q : Bool × Fin n × Fin n, ⟪cls μ (Rd (bs p) (Rd (bs q) f)), x⟫_ℂ =
      -⟪cls μ (Rd (bs q) f), cls μ (Rd (bs p) f)⟫_ℂ := fun p q =>
    hI n μ E.V hL hU hR _ _ (sob_Rd μ hR hS q) hS (bs p)

  let T : Fin n → Fin n → Mat n → E.V := fun a c g =>
    Rd (bs (true, a, c)) (Rd (bs (true, c, a)) f) g - Rd (bs (false, a, c)) (Rd (bs (false, c, a)) f) g
  have hT : ∀ a c, MemLp (fun y : G n => T a c y.val) 2 μ := fun a c => (hd _ _).sub (hd _ _)
  have hOm : ∀ g ∈ GLs n, Om f g = ∑ a, ∑ c, T a c g := by
    intro g hg
    rw [GlobalTheory.CompanionTheory.Casimir.omFormula n E.V f hS.1 g hg]
    simp only [T, basis_true_eq_single, bs_f]
  have hsumc : ∀ a, MemLp (fun y : G n => ∑ c, T a c y.val) 2 μ ∧
      cls μ (fun g => ∑ c, T a c g) = ∑ c, cls μ (T a c) := fun a =>
    cls_sum μ _ (T a) fun c _ => hT a c
  have hsum := cls_sum μ Finset.univ (fun a g => ∑ c, T a c g) fun a _ => (hsumc a).1
  have hcls : cls μ (Om f) = ∑ a, ∑ c, cls μ (T a c) := by
    have h1 : cls μ (fun g => ∑ a, ∑ c, T a c g) = cls μ (Om f) :=
      cls_congr μ hsum.1 fun g hg => (hOm g hg).symm
    rw [← h1, hsum.2]
    exact Finset.sum_congr rfl fun a _ => (hsumc a).2

  have hterm : ∀ a c, (⟪cls μ (T a c), x⟫_ℂ).re ≤ (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4 * ‖x‖ ^ 2 := by
    intro a c
    set u := cls μ (Rd (bs (true, a, c)) f) with hu
    set u' := cls μ (Rd (bs (true, c, a)) f) with hu'
    set v := cls μ (Rd (bs (false, a, c)) f) with hv
    set v' := cls μ (Rd (bs (false, c, a)) f) with hv'
    have e1 : (⟪cls μ (T a c), x⟫_ℂ).re = -(⟪u', u⟫_ℂ).re + (⟪v', v⟫_ℂ).re := by
      have : cls μ (T a c) = _ := cls_sub μ (hd (true, a, c) (true, c, a)) (hd (false, a, c) (false, c, a))
      rw [this, inner_sub_left, hip, hip]
      simp [hu, hu', hv, hv']
    have b1 : ‖u - u'‖ ≤ ‖BY a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_sub u u', cls_ae μ (mem1 μ hS (true, a, c)), cls_ae μ (mem1 μ hS (true, c, a))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ← hBY a c f hCE _ (val_mem y), Rd_sub, basis_true_eq_single, basis_true_eq_single]
    have b2 : ‖v + v'‖ ≤ ‖BZ a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_add v v', cls_ae μ (mem1 μ hS (false, a, c)), cls_ae μ (mem1 μ hS (false, c, a))] with y h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, ← hBZ a c f hCE _ (val_mem y), Rd_add, bs_f, bs_f]
    have p1 := pol_sub u u'
    have p2 := pol_add v v'
    have s1 : ‖u - u'‖ ^ 2 ≤ (‖BY a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b1 2
    have s2 : ‖v + v'‖ ^ 2 ≤ (‖BZ a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b2 2
    rw [e1]
    nlinarith
  rw [hcls, sum_inner, Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sum_inner, Complex.re_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun c _ => hterm a c

theorem secBound_main : SecBound := secBound GlobalTheory.T.sobolev_integration_by_parts

end GlobalTheory.CompanionTheory.SecBd
