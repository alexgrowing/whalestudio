import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSecP

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

def secK (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) : C(KR n, ℂ) :=
  ⟨fun k => sL R ((k : GR n) * y), (hL.cont R).comp (continuous_subtype_val.mul continuous_const)⟩

@[simp] theorem secK_apply (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) (k : KR n) :
    secK hL R y k = sL R ((k : GR n) * y) := rfl

def Ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) : Submodule ℂ (PX m n) where
  carrier := {R | ∀ y, L (secK hL R y) = 0}
  add_mem' := by
    intro R R' hR hR' y
    have : secK hL (R + R') y = secK hL R y + secK hL R' y := by ext k; simp
    rw [this, map_add, hR y, hR' y, add_zero]
  zero_mem' := by
    intro y
    have : secK hL 0 y = 0 := by ext k; simp
    rw [this, map_zero]
  smul_mem' := by
    intro a R hR y
    have : secK hL (a • R) y = a • secK hL R y := by ext k; simp
    rw [this, map_smul, hR y, smul_zero]

theorem ann_of_quot (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) {R D : PX m n} (hR : R ∈ Ann hL L)
    (hq : ∀ y : GR n, ∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL D ((k : GR n) * y)‖ ≤ δ) :
    D ∈ Ann hL L := by
  intro y
  have hR' : ∀ y', L (secK hL R y') = 0 := hR
  obtain ⟨f, hf⟩ := hq y
  set F : ℝ → C(KR n, ℂ) := fun s => (s : ℂ)⁻¹ • (secK hL R (y * f s) - secK hL R y) with hF
  have hU : TendstoUniformly (fun s (k : KR n) => F s k) (secK hL D y) (𝓝[≠] (0:ℝ)) := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨η, hη, hs⟩ := hf (δ / 2) (by linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨η, hη, ?_⟩
    intro s hs1 hs2 k
    have hs0 : s ≠ 0 := hs2
    have habs : |s| < η := by simpa [Real.dist_eq] using hs1
    have hk := hs s hs0 habs k
    rw [dist_comm, dist_eq_norm]
    have e : F s k = (sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s := by
      simp [hF, secK_apply, mul_assoc, div_eq_inv_mul]
    rw [e, secK_apply]
    linarith
  have hT : Filter.Tendsto F (𝓝[≠] (0:ℝ)) (𝓝 (secK hL D y)) :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr (fun K _ => hU.tendstoUniformlyOn)
  have hL0 : Filter.Tendsto (fun s => L (F s)) (𝓝[≠] (0:ℝ)) (𝓝 (L (secK hL D y))) :=
    (L.continuous.tendsto _).comp hT
  have hz : (fun s => L (F s)) = fun _ => (0 : ℂ) := by
    funext s
    simp only [hF, map_smul, map_sub, hR' (y * f s), hR' y, sub_self, smul_zero]
  rw [hz] at hL0
  exact tendsto_nhds_unique hL0 tendsto_const_nhds

theorem t_ne (hL : LocData ε c t p q e sL ρ) : t ≠ 0 := by
  intro h0
  have hc := hL.cpos
  rcases hL.sign with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

def lin (Φ : Fin n → Fin n → PX m n) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Φ j i

theorem lin_add (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H + H') = lin Φ H + lin Φ H' := by
  simp only [lin, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem lin_sub (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H - H') = lin Φ H - lin Φ H' := by
  simp only [lin, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lin_smul (Φ : Fin n → Fin n → PX m n) (z : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) : lin Φ (z • H) = z • lin Φ H := by
  simp only [lin, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem lin_single (Φ : Fin n → Fin n → PX m n) (a b : Fin n) :
    lin Φ (Matrix.single a b (1 : ℂ)) = Φ b a := by
  classical
  simp [lin, Matrix.single_apply, ite_and, apply_ite C, ite_mul, Finset.sum_ite_eq]

theorem herm1 (a b : Fin n) : (Matrix.single a b (1 : ℂ) + Matrix.single b a 1).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, add_comm]

theorem herm2 (a b : Fin n) : (Complex.I • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
    star_one, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem entry_of_lin (S : Submodule ℂ (PX m n)) (Φ : Fin n → Fin n → PX m n) (R : PX m n)
    (h : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin Φ H * R ∈ S) (a b : Fin n) :
    Φ b a * R ∈ S := by
  have h1 := h _ (herm1 a b)
  have h2 := h _ (herm2 a b)
  rw [lin_add, lin_single, lin_single] at h1
  rw [lin_smul, lin_sub, lin_single, lin_single] at h2
  have hI : (-(Complex.I / 2)) * Complex.I = (1 / 2 : ℂ) := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have h3 : Φ b a * R = (1 / 2 : ℂ) • ((Φ b a + Φ a b) * R) + (-(Complex.I / 2)) • ((Complex.I • (Φ b a - Φ a b)) * R) := by
    rw [smul_mul_assoc, smul_smul, hI, add_mul, sub_mul]
    module
  rw [h3]
  exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

theorem mon_le_adjoin (ε : Fin m → Bool) (d : ℕ) {R : PX m n} (hR : R ∈ Mon ε d) :
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have hle : Mon ε d ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) := by
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    apply Subalgebra.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  exact hle hR

theorem gen_mul_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer) (d : ℕ)
    (hd : Mon ε d ≤ Ann hL L) {R : PX m n} (hR : R ∈ Mon ε d) (k : Bool × Fin n × Fin n) :
    gen ε k * R ∈ Ann hL L := by
  have hRA : R ∈ Ann hL L := hd hR
  have hRad := mon_le_adjoin ε d hR
  have hN : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qp ε j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDN : DN ε t H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).1)
    have ht : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (t_ne hL))
    have e1 : lin (fun j i => Qp ε j i) H * R = (Complex.I * (t : ℂ))⁻¹ • DN ε t H R := by
      rw [lin, DN, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ hDN
  have hM : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qb ε true j i + Qb ε false j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDM : DM ε c H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).2)
    have hE : eulH H R ∈ Ann hL L := hd (eulH_mon ε H d hR)
    have hc : (2 * (c : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hL.cpos.ne')
    have e1 : lin (fun j i => Qb ε true j i + Qb ε false j i) H * R
        = (2 * (c : ℂ))⁻¹ • (((m : ℂ) * H.trace) • R + eulH H R - DM ε c H R) := by
      rw [lin, DM, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, sub_sub_cancel, ← mul_assoc, ← mul_assoc,
        ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ ((Ann hL L).sub_mem ((Ann hL L).add_mem ((Ann hL L).smul_mem _ hRA) hE) hDM)
  obtain ⟨b, i, j⟩ := k
  have hP := entry_of_lin (Ann hL L) (fun j i => Qp ε j i) R hN j i
  have hS := entry_of_lin (Ann hL L) (fun j i => Qb ε true j i + Qb ε false j i) R hM j i
  have hsum := (Ann hL L).add_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  have hdif := (Ann hL L).sub_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  cases b
  · convert hdif using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module
  · convert hsum using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module

theorem mon_le_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer)
    (h1 : (1 : PX m n) ∈ Ann hL L) : ∀ d, Mon ε d ≤ Ann hL L := by
  intro d
  induction d with
  | zero =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hl0
    simpa using h1
  | succ d ih =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    cases l with
    | nil => simpa using h1
    | cons a l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
      rw [List.map_cons, List.prod_cons]
      have hM : (List.map (gen ε) l).prod ∈ Mon ε d := Submodule.subset_span ⟨l, hl, rfl⟩
      exact gen_mul_ann hL L hD d ih hM a

end PositivityTheory.Rg.Sw.AbsSt.CycP

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.CycP

theorem cycSec_of (hC : Cyc) (hZ : SecZero) (hD : SecDer) : CycSec := by
  intro m n ε c t p q e sL ρ hL L hL0 P h hh
  have h1 : (1 : PX m n) ∈ Ann hL L := by
    intro y
    refine hL0 y _ fun k => ?_
    simp [hL.vac]
  obtain ⟨R, hR, hPR⟩ := hC m n ε c hL.cpos P
  obtain ⟨d, hd⟩ := adjoin_le ε hR
  have hRA := mon_le_ann hL L hD h1 d hd
  have hz := (hZ m n ε c t p q e sL ρ hL (P - R)).1 hPR
  have : h = secK hL R 1 := by
    ext k
    have := hz (k : GR n)
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    rw [hh, secK_apply, mul_one, this]
  rw [this]
  exact hRA 1

end PositivityTheory.Rg.Sw.AbsSt
