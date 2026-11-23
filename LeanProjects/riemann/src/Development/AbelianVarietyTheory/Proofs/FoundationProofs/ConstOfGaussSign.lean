import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.EquivConst

open GlobalTheory.SymConst

def GaussSign (D : D7) : Prop := ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M] (φ : M → ℂ) (β : M → M → ℂ), (∀ x, φ x ≠ 0) → (∀ x y, φ (x + y) = φ x * φ y * β x y) → (∀ x x' y, β (x + x') y = β x y * β x' y) → (∀ (a : 𝓞 D.host.E) x y, β (a • x) y = β x (GlobalTheory.InertSign.sgO D a • y)) → (∀ x, (∀ y, β x y = 1) → x = 0) → (∀ x, ∃ χ : 𝓞 D.host.E → ℂ, (∀ a b, χ (a + b) = χ a * χ b) ∧ ∀ a, φ (a • x) = χ (a * GlobalTheory.InertSign.sgO D a)) → ∃ r : ℝ, 0 < r ∧ ∑ᶠ x, φ x = sgn D (Nat.card M) * (r : ℂ)

theorem finsum_comp_surj {G K : Type} [AddCommGroup G] [AddCommGroup K] [Finite G] (p : G →+ K)
    (hp : Function.Surjective p) (f : K → ℂ) :
    ∃ n : ℕ, 0 < n ∧ ∑ᶠ g, f (p g) = n * ∑ᶠ k, f k := by
  haveI : Finite K := Finite.of_surjective p hp
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite K
  refine ⟨(Finset.univ.filter fun g => p g = 0).card, Finset.card_pos.2 ⟨0, by simp⟩, ?_⟩
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_fiberwise (s := Finset.univ) (g := fun g => p g)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f k) (fun g hg => by rw [(Finset.mem_filter.1 hg).2]),
    Finset.sum_const, nsmul_eq_mul, AddMonoidHom.card_fiber_eq_of_mem_range p (hp k) (hp 0)]

theorem gauss_quot (D : D7) (hG : GaussSign D) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] (R : Submodule (𝓞 D.host.E) M)
    (N : AddSubgroup M) [Finite (M ⧸ N)] (hNR : N ≤ R.toAddSubgroup) (φ : M → ℂ) (β : M → M → ℂ)
    (h0 : ∀ x, φ x ≠ 0) (hadd : ∀ x y, φ (x + y) = φ x * φ y * β x y)
    (hβ : ∀ x x' y, β (x + x') y = β x y * β x' y)
    (hσ : ∀ (a : 𝓞 D.host.E) x y, β (a • x) y = β x (GlobalTheory.InertSign.sgO D a • y))
    (hrad : ∀ x, (∀ y, β x y = 1) → x ∈ R) (hper : ∀ x, ∀ w ∈ R, φ (x + w) = φ x)
    (hχ : ∀ x, ∃ χ : 𝓞 D.host.E → ℂ, (∀ a b, χ (a + b) = χ a * χ b) ∧
      ∀ a, φ (a • x) = χ (a * GlobalTheory.InertSign.sgO D a)) :
    ∃ r : ℝ, 0 < r ∧ ∑ᶠ q : M ⧸ N, φ q.out = sgn D R.toAddSubgroup.index * (r : ℂ) := by
  have hcongr : ∀ x y : M, R.mkQ x = R.mkQ y → φ x = φ y := fun x y h => by
    have := hper y (x - y) ((Submodule.Quotient.eq R).1 h)
    rwa [add_sub_cancel] at this
  obtain ⟨o, ho⟩ := (R.mkQ_surjective).hasRightInverse
  have e1 : ∀ x, φ (o (R.mkQ x)) = φ x := fun x => hcongr _ _ (ho _)
  have e2 : ∀ x y, β (o (R.mkQ x)) (o (R.mkQ y)) = β x y := fun x y => by
    have h1 := hadd (o (R.mkQ x)) (o (R.mkQ y))
    rw [e1, e1, hcongr _ (x + y) (by rw [map_add, map_add, ho, ho]), hadd] at h1
    exact (mul_left_cancel₀ (mul_ne_zero (h0 x) (h0 y)) h1).symm
  let p : M ⧸ N →+ M ⧸ R := QuotientAddGroup.lift N R.mkQ.toAddMonoidHom fun x hx =>
    (Submodule.Quotient.mk_eq_zero R).2 (hNR hx)
  have hp0 : ∀ x : M, p (x : M ⧸ N) = R.mkQ x := fun x => rfl
  have hp : Function.Surjective p := fun k => ⟨(o k : M ⧸ N), (hp0 _).trans (ho k)⟩
  haveI : Finite (M ⧸ R) := Finite.of_surjective p hp
  obtain ⟨r, hr, hs⟩ := hG (M ⧸ R) (fun k => φ (o k)) (fun k l => β (o k) (o l)) (fun _ => h0 _)
    (fun k l => by
      obtain ⟨x, rfl⟩ := R.mkQ_surjective k
      obtain ⟨y, rfl⟩ := R.mkQ_surjective l
      rw [← map_add, e1, e1, e1, e2, hadd])
    (fun k k' l => by
      obtain ⟨x, rfl⟩ := R.mkQ_surjective k
      obtain ⟨x', rfl⟩ := R.mkQ_surjective k'
      obtain ⟨y, rfl⟩ := R.mkQ_surjective l
      rw [← map_add, e2, e2, e2, hβ])
    (fun a k l => by
      obtain ⟨x, rfl⟩ := R.mkQ_surjective k
      obtain ⟨y, rfl⟩ := R.mkQ_surjective l
      rw [← map_smul, ← map_smul, e2, e2, hσ])
    (fun k hk => by
      obtain ⟨x, rfl⟩ := R.mkQ_surjective k
      exact (Submodule.Quotient.mk_eq_zero R).2 (hrad x fun y => by rw [← e2]; exact hk _))
    (fun k => by
      obtain ⟨x, rfl⟩ := R.mkQ_surjective k
      obtain ⟨χ, h1, h2⟩ := hχ x
      exact ⟨χ, h1, fun a => by rw [← map_smul, e1, h2]⟩)
  obtain ⟨n, hn, hsum⟩ := finsum_comp_surj p hp fun k => φ (o k)
  refine ⟨n * r, by positivity, ?_⟩
  have e3 : ∀ q : M ⧸ N, φ q.out = φ (o (p q)) := fun q => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q, hp0, e1]
  simp only [e3]
  rw [hsum, hs]
  have : Nat.card (M ⧸ R) = R.toAddSubgroup.index := rfl
  rw [this]
  push_cast
  ring

theorem gauss_sign (D : D7) (hG : GaussSign D) {V : Type} [AddCommGroup V] [Module ℂ V] (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (s : ℝ) (A : AddSubgroup V) (hFG : A.FG)
    (hint : ∀ x ∈ A, ∀ y ∈ A, ∃ n : ℤ, (H x y).im = n)
    (hsd : ∀ x, (∀ y ∈ A, ∃ n : ℤ, (H x y).im = n) → x ∈ A)
    (hq : ∀ x ∈ A, ∃ n : ℤ, s * (H x x).re = n)
    (hsemi : ∀ x ∈ A, ∀ y ∈ A, ∃ k : ℤ,
      s * (H (x + y) (x + y)).re = s * (H x x).re + s * (H y y).re - (H x y).im + 2 * k)
    (a C : V →ₗ[ℂ] V) (ha : ∀ x y, H (a x) (a y) = H x y)
    (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x)) (hsurj : ∀ x, ∃ z, x = z - a z)
    (m : ℕ) (hm0 : 0 < m) (hm : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (T : 𝓞 D.host.E → V →ₗ[ℂ] V) (hT1 : ∀ x, T 1 x = x) (hTm : ∀ b c x, T (b * c) x = T b (T c x))
    (hTa : ∀ b c x, T (b + c) x = T b x + T c x) (hT0 : ∀ x, T 0 x = 0)
    (hTA : ∀ b, ∀ x ∈ A, T b x ∈ A) (hTc : ∀ b x, T b (a x) = a (T b x))
    (hTH : ∀ b x y, H (T b x) y = H x (T (GlobalTheory.InertSign.sgO D b) y)) :
    ∃ r : ℝ, 0 < r ∧ ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A,
      (-1 : ℂ) ^ (round (s * (H ((q.out : A) : V) ((q.out : A) : V)).re)) *
        Complex.exp (-(Real.pi : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) =
      sgn D ((A.map (LinearMap.id - a : V →ₗ[ℂ] V).toAddMonoidHom).relIndex A) * (r : ℂ) := by
  have hcomm : ∀ b x, C (T b x) = T b (C x) := by
    intro b x
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hC, map_sub, hTc, hC, map_smul, map_add, hTc]
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
  letI : Module (𝓞 D.host.E) A :=
    { smul := fun b x => ⟨T b x, hTA b x x.2⟩
      one_smul := fun x => Subtype.ext (hT1 x)
      mul_smul := fun b c x => Subtype.ext (hTm b c x)
      smul_zero := fun b => Subtype.ext (map_zero (T b))
      smul_add := fun b x y => Subtype.ext (map_add (T b) (x : V) (y : V))
      add_smul := fun b c x => Subtype.ext (hTa b c x)
      zero_smul := fun x => Subtype.ext (hT0 x) }
  have hsm : ∀ (b : 𝓞 D.host.E) (x : A), ((b • x : A) : V) = T b x := fun _ _ => rfl
  have hR0 : ∀ w : A, w ∈ (A.map (LinearMap.id - a : V →ₗ[ℂ] V).toAddMonoidHom).addSubgroupOf A ↔
      ∃ y ∈ A, y - a y = (w : V) := fun w => by
    simp [AddSubgroup.mem_addSubgroupOf]
  let R : Submodule (𝓞 D.host.E) A :=
    { (A.map (LinearMap.id - a : V →ₗ[ℂ] V).toAddMonoidHom).addSubgroupOf A with
      smul_mem' := fun b w hw => by
        obtain ⟨y, hy, hyw⟩ := (hR0 w).1 hw
        exact (hR0 _).2 ⟨T b y, hTA b y hy, by rw [hsm, ← hyw, map_sub, hTc]⟩ }
  have e6 : ∀ x w, (H (C (x + w)) (x + w)).im = (H (C x) x).im + (H (C w) w).im + 2 * (H (C x) w).im := fun x w => by
    have := hCim x w
    simp; linarith
  refine gauss_quot D hG A R _ ?_ (fun x : A => ex (ψ x)) (fun x y : A => ex (-(H x y).im - 2 * (H (C x) y).im))
    (fun x => Complex.exp_ne_zero _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := (hmem w).1 hw
    obtain ⟨y, hy, -, hyv⟩ := hm v hv
    exact (hR0 w).2 ⟨y, hy, hyv.symm.trans hvw⟩
  · intro x y
    obtain ⟨k, hk⟩ := hsemi x x.2 y y.2
    rw [← ex_add, ← ex_add]
    refine ex_congr k ?_
    simp only [ψ, AddSubgroup.coe_add]
    rw [hk, e6]
    ring
  · intro x x' y
    rw [← ex_add]
    congr 1
    simp only [AddSubgroup.coe_add, map_add, LinearMap.add_apply, Complex.add_im]
    ring
  · intro b x y
    simp only [hsm, hcomm, hTH]
  · intro x hx
    obtain ⟨z, hz⟩ := hsurj x
    refine (hR0 x).2 ⟨z, hsd z fun y hy => ?_, hz.symm⟩
    have h1 := hx ⟨y, hy⟩
    have h2 : ex 0 = 1 := by simp [ex]
    obtain ⟨k, hk⟩ := ex_eq (h1.trans h2.symm)
    refine ⟨-k, ?_⟩
    rw [hz, hC] at hk
    simp at hk
    push_cast
    linarith
  · intro x w hw
    obtain ⟨y, hy, hw'⟩ := (hR0 w).1 hw
    replace hw' := hw'.symm
    have hay : a y ∈ A := by
      have := sub_mem hy w.2
      rwa [hw', sub_sub_cancel] at this
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
    have e7 := e6 x w
    have e8 := hCim x w
    obtain ⟨k4, h4⟩ := hint x x.2 _ hay
    obtain ⟨k5, h5⟩ := hint y hy _ hay
    refine ex_congr (k1 - k2 + k4 + k5) ?_
    simp only [ψ, AddSubgroup.coe_add]
    push_cast
    linarith
  · intro x
    refine ⟨fun c => ex (s * (H x (T c x)).re - (H (C x) (T c x)).im), fun b c => ?_, fun b => ?_⟩
    · rw [← ex_add]
      congr 1
      simp only [hTa, map_add, Complex.add_im, Complex.add_re]
      ring_nf
    · simp only [ψ, hsm, hcomm, hTH]
      rw [mul_comm b, hTm]

theorem hf_scal {D : D7} {N N' : ℕ} (T : Tor D) (b : D.host.E) (x y : VC D N N') :
    Hf D T (scal D N N' b x) y = Hf D T x (scal D N N' (D.host.conj b) y) := by
  simp only [Hf, scal_apply, GlobalTheory.InertSign.embT_conj, map_mul, Complex.conj_conj]
  simp only [mul_assoc, mul_left_comm]

theorem const_of_gaussSign : ∀ (D : D7) (_ : GaussSign D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → (∀ (b : 𝓞 D.host.E), ∀ x ∈ A, scal D N N' (b : D.host.E) x ∈ A) → (∀ (b : D.host.E) x, u (scal D N N' b x) = scal D N N' b (u x)) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = (sgn D ((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A) * ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))) • Iop D (tor0 D cc δ) A A₁ th := by
  intro D hG cc δ hc N N' A A₁ hA hA₁ u hu huA hdt ⟨m, hm0, hm⟩ hsA hsu th hth
  by_cases h0 : th = 0
  · subst h0
    funext z
    simp [Iop, U]
  obtain ⟨-, -, hint, hsd, hFG, -, hq⟩ :=
    ThetaLine.theta_line D (InducedType.induced_type D).1 cc δ hc N N' A hA
  set a : VC D N N' →ₗ[ℂ] VC D N N' := (u.symm : VC D N N' →ₗ[ℂ] VC D N N') with ha
  let e := LinearMap.equivOfDetNeZero _ hdt
  have he : ∀ x, e x = x - u.symm x := fun x => rfl
  let C : VC D N N' →ₗ[ℂ] VC D N N' := ((1 / 2 : ℂ) • (LinearMap.id + a)) ∘ₗ (e.symm : VC D N N' →ₗ[ℂ] VC D N N')
  have hC : ∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x) := fun x => by
    rw [← he]; simp [C, ha]
  have hcom : ∀ (b : D.host.E) x, scal D N N' b (a x) = a (scal D N N' b x) := by
    intro b x
    apply u.injective
    rw [hsu]; simp [ha]
  obtain ⟨c, r, hc1, hr, hcr, hfin⟩ := GlobalTheory.UnitaryTheta.Constant.pull_eq_gauss_smul_intertwiner D cc δ hc N N' A A₁ hA hA₁ u hu huA hdt C hC m hm0 hm th hth h0
  obtain ⟨ρ, hρ, hsum⟩ := gauss_sign D hG (hfL (tor0 D cc δ)) (hfL_swap _) (Real.sqrt D.host.d / 2) A hFG hint hsd hq
    (semi _ A hq th hth h0) a C (fun x y => by rw [hfL_apply, ← hu]; simp [ha, hfL_apply]) hC
    (fun x => ⟨e.symm x, (e.apply_symm_apply x).symm.trans (he _)⟩) m hm0 hm
    (fun b => scal D N N' (b : D.host.E))
    (fun x => by funext τ i j; simp [scal_apply])
    (fun b c x => by funext τ i j; simp [scal_apply, mul_assoc])
    (fun b c x => by funext τ i j; simp [scal_apply, add_mul])
    (fun x => by funext τ i j; simp [scal_apply]) hsA (fun b x => hcom b x)
    (fun b x y => hf_scal _ _ x y)
  set ε := sgn D ((A.map (LinearMap.id - a).toAddMonoidHom).relIndex A) with hε
  have hε1 : ‖ε‖ = 1 := by simp [hε, sgn]
  have hcr' : c = r * (LinearMap.det (LinearMap.id - a))⁻¹ * (ε * ρ) := by rw [hcr, ← hsum]; rfl
  rw [hfin]
  congr 1
  have hn : r * ρ = ‖LinearMap.det (LinearMap.id - a)‖ := by
    rw [hcr'] at hc1
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hρ, hε1,
      one_mul] at hc1
    have := norm_ne_zero_iff.2 hdt
    field_simp at hc1
    exact hc1
  rw [hcr', ← hn]
  push_cast
  ring

end GlobalTheory.EquivConst
