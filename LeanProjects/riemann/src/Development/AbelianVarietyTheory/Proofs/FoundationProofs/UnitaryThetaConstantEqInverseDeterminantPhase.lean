import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumQuotientNonnegOfSwapConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PullEqGaussSmulIntertwiner
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SymConst

def ex (t : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * t)

theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_int (n : ℤ) : ex n = (-1 : ℂ) ^ n := by
  rw [ex, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]; congr 1; push_cast; ring

theorem ex_congr {s t : ℝ} (k : ℤ) (h : s = t + 2 * k) : ex s = ex t := by
  have : (2 * k : ℝ) = ((2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [h, ex_add, this, ex_int, zpow_mul]; simp

theorem ex_neg (t : ℝ) : ex (-t) = (starRingEnd ℂ) (ex t) := by
  rw [ex, ex, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

theorem ex_eq {s t : ℝ} (h : ex s = ex t) : ∃ k : ℤ, s = t + 2 * k := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨k, ?_⟩
  have h2 := congrArg Complex.im hk
  simp at h2
  have := Real.pi_pos
  apply mul_left_cancel₀ this.ne'
  linarith

theorem gauss_nonneg {V : Type} [AddCommGroup V] [Module ℂ V] (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (s : ℝ) (A : AddSubgroup V) (hFG : A.FG)
    (hint : ∀ x ∈ A, ∀ y ∈ A, ∃ n : ℤ, (H x y).im = n)
    (hsd : ∀ x, (∀ y ∈ A, ∃ n : ℤ, (H x y).im = n) → x ∈ A)
    (hq : ∀ x ∈ A, ∃ n : ℤ, s * (H x x).re = n)
    (hsemi : ∀ x ∈ A, ∀ y ∈ A, ∃ k : ℤ,
      s * (H (x + y) (x + y)).re = s * (H x x).re + s * (H y y).re - (H x y).im + 2 * k)
    (a C : V →ₗ[ℂ] V) (ha : ∀ x y, H (a x) (a y) = H x y)
    (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x)) (hsurj : ∀ x, ∃ z, x = z - a z)
    (m : ℕ) (hm0 : 0 < m) (hm : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (P S L B : V →ₗ[ℂ] V) (hPS : ∀ x ∈ A, P x ∈ A ∧ S x ∈ A) (hPP : ∀ x, P (P x) = P x)
    (hPH : ∀ x y, H (P x) y = H x (P y)) (hSS : ∀ x, S (S x) = x) (hSH : ∀ x y, H (S x) (S y) = H x y)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hPa : ∀ x, P (a x) = a (P x)) (hSa : ∀ x, S (a x) = a (S x))
    (hLB : ∀ x ∈ A, L x ∈ A ∧ B x ∈ A) (hLa : ∀ x, L (a x) = a (L x)) (hLP : ∀ x, L (P x) = P (L x))
    (hLH : ∀ x y, H (L x) (L y) = -H x y + (4 * m : ℕ) * H (B x) y) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A,
      (-1 : ℂ) ^ (round (s * (H ((q.out : A) : V) ((q.out : A) : V)).re)) *
        Complex.exp (-(Real.pi : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) = r := by
  have hcomm : ∀ Q : V →ₗ[ℂ] V, (∀ x, Q (a x) = a (Q x)) → ∀ x, Q (C x) = C (Q x) := by
    intro Q hQ x
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hC, map_sub, hQ, hC, map_smul, map_add, hQ]
  have hskew : ∀ x y, H (C x) y = -H x (C y) := by
    intro x y
    obtain ⟨z, rfl⟩ := hsurj x
    obtain ⟨w, rfl⟩ := hsurj y
    rw [hC, hC]
    simp [ha, Complex.conj_ofNat]
    ring
  have him : ∀ x y, (H y x).im = -(H x y).im := fun x y => by rw [hH x y]; simp
  have hre : ∀ x y, (H y x).re = (H x y).re := fun x y => by rw [hH x y]; simp
  have him0 : ∀ x, (H x x).im = 0 := fun x => by have := him x x; linarith
  have hCim : ∀ x y, (H (C x) y).im = (H (C y) x).im := fun x y => by
    rw [hskew x y, him x (C y)]; simp
  have hCre : ∀ x, (H (C x) x).re = 0 := fun x => by
    have h1 := congrArg Complex.re (hskew x x)
    rw [Complex.neg_re, hre (C x) x] at h1
    linarith
  have hmem : ∀ w : A, w ∈ (subLa m A).addSubgroupOf A ↔ ∃ v ∈ A, m • v = (w : V) := fun w => by
    simp [AddSubgroup.mem_addSubgroupOf, subLa]
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hFG
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hmem]
      exact ⟨x, x.2, rfl⟩
  let ψ : V → ℝ := fun x => s * (H x x).re - (H (C x) x).im
  have hφ : ∀ x : A, (-1 : ℂ) ^ (round (s * (H (x : V) (x : V)).re)) *
      Complex.exp (-(Real.pi : ℂ) * H (C (x : V)) (x : V)) = ex (ψ x) := by
    intro x
    obtain ⟨n, hn⟩ := hq x x.2
    simp only [ψ]
    rw [hn, round_intCast, sub_eq_add_neg, ex_add, ex_int, ex]
    congr 2
    rw [← Complex.re_add_im (H (C x) x), hCre]
    simp
    ring
  simp only [hφ]
  have res : ∀ Q : V →ₗ[ℂ] V, (∀ x ∈ A, Q x ∈ A) → ∃ Q' : A →+ A, ∀ x : A, (Q' x : V) = Q x := fun Q hQ =>
    ⟨(Q.toAddMonoidHom.comp A.subtype).codRestrict A fun x => hQ x x.2, fun _ => rfl⟩
  obtain ⟨P', hP'⟩ := res P fun x hx => (hPS x hx).1
  obtain ⟨S', hS'⟩ := res S fun x hx => (hPS x hx).2
  obtain ⟨L', hL'⟩ := res L fun x hx => (hLB x hx).1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  refine GlobalTheory.finsum_quotient_nonneg_of_swap_conj A _ (fun x : A => ex (ψ x))
    P' S' L' ?_ ?_ ?_ (fun x => Subtype.ext (by simp [hP', hPP])) (fun x => Subtype.ext (by simp [hS', hSS]))
    (fun x => Subtype.ext (by simp [hP', hS', hSP])) (fun x => Subtype.ext (by simp [hP', hL', hLP])) ?_ ?_ ?_
  · intro x w hw
    obtain ⟨v, hv, hvw⟩ := (hmem w).1 hw
    obtain ⟨y, hy, hay, hyv⟩ := hm v hv
    have hw' : (w : V) = y - a y := hvw.symm.trans hyv
    obtain ⟨k1, h1⟩ := hsemi x x.2 w w.2
    obtain ⟨k2, h2⟩ := hsemi w w.2 _ hay
    obtain ⟨k3, h3⟩ := hint x x.2 y hy
    have e1 : (w : V) + a y = y := by rw [hw']; abel
    rw [e1, ha] at h2
    have e2 : (H (C w) x).im = -((H x y).im + (H x (a y)).im) / 2 := by
      rw [hw', hC, him y x, him (a y) x]; simp; ring
    have e3 : (H (C w) w).im = -(H y (a y)).im := by
      have := him y (a y)
      rw [hw', hC]; simp [ha, him0]; linarith
    have e4 : (H w (a y)).im = (H y (a y)).im := by rw [hw']; simp [him0]
    have e5 : (H x w).im = (H x y).im - (H x (a y)).im := by rw [hw']; simp
    have e6 : (H (C (x + w)) (x + w)).im = (H (C x) x).im + (H (C w) w).im + 2 * (H (C w) x).im := by
      have := hCim x w
      simp; linarith
    obtain ⟨k4, h4⟩ := hint x x.2 _ hay
    obtain ⟨k5, h5⟩ := hint y hy _ hay
    refine ex_congr (k1 - k2 + k4 + k5) ?_
    simp only [ψ, AddSubgroup.coe_add]
    push_cast
    linarith
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := (hmem w).1 hw
    exact ⟨(hmem _).2 ⟨P v, (hPS v hv).1, by rw [hP', ← hvw, map_nsmul]⟩,
      (hmem _).2 ⟨S v, (hPS v hv).2, by rw [hS', ← hvw, map_nsmul]⟩⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨v, hv, hvw⟩ := (hmem _).1 hx
      rw [hL'] at hvw
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
      refine (hmem _).2 ⟨(m : ℂ)⁻¹ • (x : V), hsd _ fun y hy => ?_, ?_⟩
      · obtain ⟨k1, h1⟩ := hint v hv _ (hLB y hy).1
        obtain ⟨k2, h2⟩ := hint _ (hLB x x.2).2 y hy
        have h3 := congrArg Complex.im (hLH x y)
        rw [← hvw] at h3
        simp at h3
        refine ⟨4 * k2 - k1, ?_⟩
        have : ((m : ℂ))⁻¹ = ((m⁻¹ : ℝ) : ℂ) := by simp
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, this, Complex.im_ofReal_mul]
        push_cast
        field_simp
        rw [h1, h2] at h3
        linarith
      · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hmC, one_smul]
    · intro hx
      obtain ⟨v, hv, hvw⟩ := (hmem _).1 hx
      exact (hmem _).2 ⟨L v, (hLB v hv).1, by rw [hL', ← hvw, map_nsmul]⟩
  · intro x
    rw [← ex_add]
    congr 1
    simp only [ψ, AddSubgroup.coe_sub, hP']
    have e1 : H (P x) (P x) = H x (P x) := by rw [hPH, hPP]
    have e2 : H (C (P x)) (P x) = H (C x) (P x) := by rw [← hcomm P hPa, hPH, hPP]
    have e3 : H (C (P x)) x = H (C x) (P x) := by rw [← hcomm P hPa, hPH]
    have e4 := hPH x x
    simp only [map_sub, LinearMap.sub_apply, e1, e2, e3, e4, Complex.sub_re, Complex.sub_im]
    ring
  · intro x
    simp only [ψ, hS']
    rw [← hcomm S hSa, hSH, hSH]
  · intro x
    rw [← ex_neg]
    simp only [ψ, hL']
    rw [← hcomm L hLa, hLH, hLH]
    obtain ⟨y, hy, hay, hyv⟩ := hm x x.2
    have e1 : (2 * m : ℂ) • C x = y + a y := by
      have := hC y
      rw [← hyv, ← Nat.cast_smul_eq_nsmul ℂ, map_smul] at this
      rw [mul_smul, this, smul_smul]; simp
    obtain ⟨k1, h1⟩ := hint _ (hLB _ (add_mem hy hay)).2 x x.2
    rw [← e1] at h1
    obtain ⟨k2, h2⟩ := hq _ (add_mem (hLB x x.2).2 x.2)
    obtain ⟨k3, h3⟩ := hq _ (hLB x x.2).2
    obtain ⟨k4, h4⟩ := hq _ x.2
    have e2 := hre (B x) x
    simp [e2] at h1 h2
    refine ex_congr (m * (k2 - k3 - k4) - k1) ?_
    simp
    rw [← h1, ← h2, ← h3, ← h4]
    ring

variable {D : D7} {N N' : ℕ}

def hfL (T : Tor D) : VC D N N' →ₗ[ℂ] VC D N N' →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (Hf D T)
    (fun x y z => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_add_left, add_div])
    (fun c x y => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_smul_left, RingHom.id_apply, smul_eq_mul, mul_div_assoc])
    (fun x y z => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_add_right, add_div])
    (fun c x y => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_smul_right, smul_eq_mul]; ring)

theorem hfL_apply (T : Tor D) (x y : VC D N N') : hfL T x y = Hf D T x y := rfl

theorem hfL_swap (T : Tor D) (x y : VC D N N') : hfL T y x = (starRingEnd ℂ) (hfL T x y) := by
  simp [hfL_apply, Hf, Complex.conj_ofReal, mul_comm]

theorem semi (T : Tor D) (A : AddSubgroup (VC D N N')) (hq : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (th : VC D N N' → ℂ) (hth : th ∈ ThSp D T A) (h0 : th ≠ 0) :
    ∀ x ∈ A, ∀ y ∈ A, ∃ k : ℤ, qH D T (x + y) = qH D T x + qH D T y - (Hf D T x y).im + 2 * k := by
  intro x hx y hy
  have hal : ∀ x ∈ A, al D T x = ex (qH D T x) := fun x hx => by
    obtain ⟨n, hn⟩ := hq x hx
    have e : al D T x = (-1 : ℂ) ^ (round (qH D T x)) := rfl
    rw [e, hn, round_intCast, ex_int]
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  have h1 := hth.2 x hx z
  have h2 := hth.2 y hy (z + x)
  have h3 := hth.2 _ (add_mem hx hy) z
  rw [hal _ hx] at h1
  rw [hal _ hy] at h2
  rw [hal _ (add_mem hx hy)] at h3
  simp only [U, ← hfL_apply, ← add_assoc] at h1 h2 h3
  have h4 : th (z + x + y) ≠ 0 := by
    intro h; rw [h] at h3; apply hz; rw [← h3]; simp
  apply ex_eq
  rw [← h2, ← h3] at h1
  have e : Complex.exp (-(Real.pi : ℂ) * hfL T (z + x) y - Real.pi * hfL T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * hfL T z x - Real.pi * hfL T x x / 2) =
      ex (-(hfL T x y).im) * Complex.exp (-(Real.pi : ℂ) * hfL T z (x + y) - Real.pi * hfL T (x + y) (x + y) / 2) := by
    rw [ex, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e1 := Complex.sub_conj (hfL T x y)
    rw [← hfL_swap] at e1
    simp only [map_add, LinearMap.add_apply]
    push_cast at e1 ⊢
    linear_combination (-(Real.pi : ℂ) / 2) * e1
  rw [sub_eq_add_neg, ex_add, ex_add, ← hfL_apply]
  apply mul_right_cancel₀ (mul_ne_zero h4 (Complex.exp_ne_zero
    (-(Real.pi : ℂ) * hfL T z (x + y) - Real.pi * hfL T (x + y) (x + y) / 2)))
  linear_combination -h1 + ex (qH D T x) * ex (qH D T y) * th (z + x + y) * e

theorem const_of_symm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ (P S : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x ∈ A, P x ∈ A ∧ S x ∈ A) → (∀ x, P (P x) = P x) → (∀ x y, Hf D (tor0 D cc δ) (P x) y = Hf D (tor0 D cc δ) x (P y)) → (∀ x, S (S x) = x) → (∀ x y, Hf D (tor0 D cc δ) (S x) (S y) = Hf D (tor0 D cc δ) x y) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, P (u x) = u (P x)) → (∀ x, S (u x) = u (S x)) → (∀ M : ℕ, 0 < M → ∃ L B : VC D N N' →ₗ[ℂ] VC D N N', (∀ x ∈ A, L x ∈ A ∧ B x ∈ A) ∧ (∀ x, L (u x) = u (L x)) ∧ (∀ x, B (u x) = u (B x)) ∧ (∀ x, L (P x) = P (L x)) ∧ (∀ x y, Hf D (tor0 D cc δ) (B x) y = Hf D (tor0 D cc δ) x (B y)) ∧ ∀ x y, Hf D (tor0 D cc δ) (L x) (L y) = -Hf D (tor0 D cc δ) x y + M * Hf D (tor0 D cc δ) (B x) y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))) • Iop D (tor0 D cc δ) A A₁ th := by
  intro D cc δ hc N N' A A₁ hA hA₁ u hu huA hdt ⟨m, hm0, hm⟩ P S hPS hPP hPH hSS hSH hSP hPu hSu hLB th hth
  by_cases h0 : th = 0
  · subst h0
    funext z
    simp [Iop, U]
  obtain ⟨-, -, hint, hsd, hFG, -, hq⟩ :=
    ThetaLine.theta_line D (InducedType.induced_type D).1 cc δ hc N N' A hA
  obtain ⟨L, B, hL1, hLu, -, hLP, -, hLH⟩ := hLB (4 * m) (by omega)
  set a : VC D N N' →ₗ[ℂ] VC D N N' := (u.symm : VC D N N' →ₗ[ℂ] VC D N N') with ha
  let e := LinearMap.equivOfDetNeZero _ hdt
  have he : ∀ x, e x = x - u.symm x := fun x => rfl
  let C : VC D N N' →ₗ[ℂ] VC D N N' := ((1 / 2 : ℂ) • (LinearMap.id + a)) ∘ₗ (e.symm : VC D N N' →ₗ[ℂ] VC D N N')
  have hC : ∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x) := fun x => by
    rw [← he]; simp [C, ha]
  have hcom : ∀ Q : VC D N N' →ₗ[ℂ] VC D N N', (∀ x, Q (u x) = u (Q x)) → ∀ x, Q (a x) = a (Q x) := by
    intro Q hQ x
    apply u.injective
    rw [← hQ]; simp [ha]
  obtain ⟨c, r, hc1, hr, hcr, hfin⟩ := GlobalTheory.UnitaryTheta.Constant.pull_eq_gauss_smul_intertwiner D cc δ hc N N' A A₁ hA hA₁ u hu huA hdt C hC m hm0 hm th hth h0
  obtain ⟨ρ, hρ, hsum⟩ := gauss_nonneg (hfL (tor0 D cc δ)) (hfL_swap _) (Real.sqrt D.host.d / 2) A hFG hint hsd hq
    (semi _ A hq th hth h0) a C (fun x y => by rw [hfL_apply, ← hu]; simp [ha, hfL_apply]) hC
    (fun x => ⟨e.symm x, (e.apply_symm_apply x).symm.trans (he _)⟩) m hm0 hm P S L B hPS hPP hPH hSS hSH hSP
    (hcom P hPu) (hcom S hSu) hL1 (hcom L hLu) hLP hLH
  have hcr' : c = r * (LinearMap.det (LinearMap.id - a))⁻¹ * ρ := by rw [hcr, ← hsum]; rfl
  rw [hfin]
  congr 1
  have hn : r * ρ = ‖LinearMap.det (LinearMap.id - a)‖ := by
    rw [hcr'] at hc1
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_nonneg hρ] at hc1
    have := norm_ne_zero_iff.2 hdt
    field_simp at hc1
    exact hc1
  rw [hcr', ← hn]
  push_cast
  ring

end GlobalTheory.SymConst
