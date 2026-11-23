import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplexStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatibleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.FamPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

private theorem strictAnti_lt_of_succ_lt (D : Datum H) (u v : D.La) : D.EF u v = -D.EF v u := by
  have h := D.alt (u + v)
  simp only [map_add, LinearMap.add_apply, D.alt u, D.alt v] at h
  omega

private theorem ef_w0_smul_left_swap (D : Datum H) (u y : D.La) :
    D.EF (H.w0 • y) u = D.EF (H.w0 • u) y - D.EF u y := by
  have h1 : D.EF (H.w0 • u) y = D.EF u y - D.EF u (H.w0 • y) := by
    rw [D.adj, HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub]
  rw [strictAnti_lt_of_succ_lt D (H.w0 • y) u]
  omega

private theorem ef_rt_smul_right (D : Datum H) (u v : D.La) :
    D.EF u (H.rt • v) = 2 * D.EF u (H.w0 • v) - D.EF u v := by
  have hrt : H.rt = 2 * H.w0 - 1 := by linear_combination -H.two_weight_eq_one_add_root
  rw [hrt, sub_smul, one_smul, mul_smul, two_smul, map_sub, map_add]
  ring

private theorem four_mul_ef_w0_smul_w0_smul (D : Datum H) (u v : D.La) :
    4 * D.EF (H.w0 • u) (H.w0 • v) = (1 + H.d) * D.EF u v := by
  have key : ((4 : ℕ) : 𝓞 E) * ((1 - H.w0) * H.w0) = ((1 + H.d : ℕ) : 𝓞 E) := by
    push_cast
    linear_combination (-(2 * H.w0 - 1 + H.rt)) * H.two_weight_eq_one_add_root - H.rt_sq
  have e1 : D.EF (H.w0 • u) (H.w0 • v) = D.EF u (((1 - H.w0) * H.w0) • v) := by
    rw [D.adj, HostModel.cmHost_bar_halfIntegerGenerator, smul_smul]
  have e2 : D.EF u ((((4 : ℕ) : 𝓞 E) * ((1 - H.w0) * H.w0)) • v) =
      4 * D.EF u (((1 - H.w0) * H.w0) • v) := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    norm_num
  have e3 : D.EF u (((1 + H.d : ℕ) : 𝓞 E) • v) = (1 + H.d) * D.EF u v := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  rw [e1, ← e2, key, e3]

theorem polarise (D : Datum H) (L : Submodule (𝓞 E) D.La) {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (ω c : ℂ)
    (hω : (2 * ω - 1) ^ 2 = -(H.d : ℂ)) (x : L → (Fin g → ℂ)) (hadd : ∀ a b, x (a + b) = x a + x b)
    (hrt : ∀ a, x (H.rt • a) = (2 * ω - 1) • x a)
    (hq : ∀ a : L, hermForm Hm (x a) (x a) = (D.EF (H.w0 • (a : D.La)) a : ℂ) * c) (a b : L) :
    hermForm Hm (x a) (x b) =
      (((D.EF (H.w0 • (a : D.La)) b : ℂ) - D.EF a b) + (D.EF a b : ℂ) * ω) * c := by
  have hd : H.d ≠ 0 := H.d_prime.ne_zero
  have hdC : (H.d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hconj : starRingEnd ℂ (2 * ω - 1) = -(2 * ω - 1) := GlobalTheory.EigenNorm.conj_eq_neg_of_sq hd hω
  have S1 : ∀ p q : L, hermForm Hm (x p) (x q) + hermForm Hm (x q) (x p) =
      ((D.EF (H.w0 • (p : D.La)) q : ℂ) + (D.EF (H.w0 • (q : D.La)) p : ℂ)) * c := by
    intro p q
    have h := hq (p + q)
    have hp := hq p
    have hq' := hq q
    rw [hadd, GlobalTheory.EigenNorm.hermForm_add_left, GlobalTheory.EigenNorm.hermForm_add_right,
      GlobalTheory.EigenNorm.hermForm_add_right] at h
    simp only [Submodule.coe_add, smul_add, map_add, LinearMap.add_apply, Int.cast_add] at h
    linear_combination h - hp - hq'
  have Sab := S1 a b
  have Sarb := S1 a (H.rt • b)
  rw [hrt, GlobalTheory.EigenNorm.hermForm_smul_right, GlobalTheory.EigenNorm.hermForm_smul_left, hconj] at Sarb
  set A : ℤ := D.EF (H.w0 • (a : D.La)) b with hA
  set Ee : ℤ := D.EF (a : D.La) b with hE
  set W : ℤ := D.EF (H.w0 • (a : D.La)) (H.w0 • (b : D.La)) with hW
  have g1 : ((D.EF (H.w0 • (b : D.La)) a : ℤ) : ℂ) = (A : ℂ) - Ee := by
    rw [ef_w0_smul_left_swap]; push_cast; ring
  have g2 : ((D.EF (H.w0 • (a : D.La)) ((H.rt • b : L) : D.La) : ℤ) : ℂ) = 2 * (W : ℂ) - A := by
    rw [Submodule.coe_smul, ef_rt_smul_right]; push_cast; ring
  have g3 : ((D.EF (H.w0 • ((H.rt • b : L) : D.La)) a : ℤ) : ℂ) = 2 * (W : ℂ) + A - Ee := by
    have i1 := ef_w0_smul_left_swap D (a : D.La) (H.rt • (b : D.La))
    have i2 := ef_rt_smul_right D (H.w0 • (a : D.La)) b
    have i3 := ef_rt_smul_right D (a : D.La) b
    have i4 := ef_w0_smul_left_swap D (a : D.La) (b : D.La)
    have i5 := strictAnti_lt_of_succ_lt D (a : D.La) (H.w0 • (b : D.La))
    have hz : D.EF (H.w0 • (H.rt • (b : D.La))) a = 2 * W + A - Ee := by
      linarith [i1, i2, i3, i4, i5, hA, hE, hW]
    rw [Submodule.coe_smul, hz]
    push_cast
    ring
  have g4 : (4 : ℂ) * W = (1 + (H.d : ℂ)) * Ee := by
    have := four_mul_ef_w0_smul_w0_smul D (a : D.La) (b : D.La)
    rw [hW, hE]; exact_mod_cast this
  have key : (2 * (2 * ω - 1)) * (hermForm Hm (x a) (x b) -
      (((A : ℂ) - Ee) + (Ee : ℂ) * ω) * c) = 0 := by
    linear_combination (2 * ω - 1) * Sab - Sarb + (2 * ω - 1) * c * g1 - c * g2 - c * g3 - c * g4 -
      (Ee : ℂ) * c * hω
  have hr0 : (2 * (2 * ω - 1) : ℂ) ≠ 0 := by
    intro h0
    have : (2 * ω - 1) = 0 := by linear_combination h0 / 2
    rw [this] at hω
    exact hdC (by linear_combination hω)
  have := (mul_eq_zero.mp key).resolve_left hr0
  rw [hA, hE] at this
  linear_combination this

theorem smul_of_rt {M : Type} [AddCommGroup M] [Module (𝓞 E) M] {g : ℕ} (ω : ℂ) (τ : OK H →+* ℂ) (hτ : τ (wK H) = ω)
    (x : M → (Fin g → ℂ)) (hadd : ∀ a b, x (a + b) = x a + x b) (hrt : ∀ a, x (H.rt • a) = (2 * ω - 1) • x a)
    (c : OK H) (a : M) : x ((c : 𝓞 E) • a) = τ c • x a := by
  obtain ⟨c, hc⟩ := c
  show x (c • a) = τ ⟨c, hc⟩ • x a
  have hw : ∀ a, x (H.w0 • a) = ω • x a := by
    intro a
    have h2 : x (H.w0 • a) + x (H.w0 • a) = ((2 : ℂ) * ω) • x a := by
      rw [← hadd, ← two_smul (𝓞 E), ← mul_smul, H.two_weight_eq_one_add_root, add_smul, one_smul, hadd, hrt, sub_smul, one_smul]
      abel
    funext i
    have := congrFun h2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this / 2
  let X : M →+ (Fin g → ℂ) := AddMonoidHom.mk' x hadd
  induction hc using Algebra.adjoin_induction generalizing a with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have : (⟨H.w0, _⟩ : OK H) = wK H := rfl
    rw [this, hτ, hw]
  | algebraMap r =>
    have e1 : (⟨algebraMap ℤ (𝓞 E) r, Subalgebra.algebraMap_mem _ r⟩ : OK H) = (r : OK H) := by
      apply Subtype.ext; simp
    rw [e1, map_intCast, algebraMap_smul]
    have := map_zsmul X r a
    simp only [X, AddMonoidHom.mk'_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  | add y z hy hz ihy ihz =>
    have e1 : (⟨y + z, Subalgebra.add_mem _ hy hz⟩ : OK H) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e1, map_add, add_smul, hadd, ihy, ihz, add_smul]
  | mul y z hy hz ihy ihz =>
    have e1 : (⟨y * z, Subalgebra.mul_mem _ hy hz⟩ : OK H) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e1, map_mul, mul_smul, ihy, ihz, smul_smul]

theorem char_sq (ω : ℂ) (τ : OK H →+* ℂ) (hτ : τ (wK H) = ω) : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := by
  have hw : ((wK H : OK H) : 𝓞 E) = H.w0 := rfl
  have key : ((wK H + wK H - 1) ^ 2 : OK H) = -((H.d : ℕ) : OK H) := by
    apply Subtype.ext
    push_cast [hw]
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq
  have := congrArg τ key
  rw [map_pow, map_sub, map_add, map_one, map_neg, map_natCast, hτ] at this
  linear_combination this

theorem isFam_of_isHomFamily : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp ℂ)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)), IsKForm D ε h → (∀ x ∈ L, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → PureType.IsHomFamily T.t C.P.A C.P.L C.v L (2 * ω - 1) Set.univ ψ → IsFam C T h L ψ := by
  intro hTh hLaws E _ _ _ H ω C D ε h T L ψ hK hpos hF
  obtain ⟨hmon, hadd, hlin, hrt, hpow⟩ := hF
  obtain ⟨rigC, hrigC⟩ := C.P.rigid
  obtain ⟨rigT, hrigT⟩ := T.pol.rigid
  obtain ⟨uC, HC, χC, EfC, hAHC, -, hdC1, hdC2, -, -, -, -, -⟩ := hTh C.P rigC hrigC
  obtain ⟨uT, HT, χT, EfT, hAHT, -, hdT1, hdT2, -, -, -, -, -⟩ := hTh T.pol rigT hrigT
  have hlift := fun a => GlobalTheory.HomLinear.exists_linear_of_isMonHom C.P.A T.pol.A C.P.isAb T.pol.isAb C.P.L T.pol.L
    C.P.g T.pol.g uC uT hdT1 hdT2 (ψ a) (hmon a)
  choose F hFex hFΛ hFdiff hFuniq using hlift
  have hvt : IsTangent C.v := C.basis.1 0
  obtain ⟨wv, hwv, -⟩ := hdC1 C.v hvt
  obtain ⟨τ₀, hτ₀, hτ₀c⟩ := GlobalTheory.CM.LieChar.ell_char E H ℂ ω C

  have span : ∀ z : Fin C.P.g → ℂ, ∃ s : ℂ, z = s • wv := by
    intro z
    obtain ⟨vz, ⟨hvz, hdz⟩, -⟩ := hdC2 z
    obtain ⟨cc, hcc, -⟩ := C.basis.2 vz hvz
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb C.P.A C.P.L C.P.g 1 uC ![wv] ![C.v] cc vz
      (fun i => by fin_cases i; exact hvt) (fun i => by fin_cases i; exact hwv) hcc
    refine ⟨cc 0, ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hd
    exact (hdC1 vz hvz).unique hdz hd

  have hG : ∀ c : OK H, ∃ G : (Fin C.P.g → ℂ) →ₗ[ℂ] (Fin C.P.g → ℂ),
      (∀ z, uC.ex (G z) = uC.ex z ≫ C.act.act c) ∧ G wv = τ₀ c • wv := by
    intro c
    obtain ⟨G, hGex, -, hGdiff, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom C.P.A C.P.A C.P.isAb C.P.isAb C.P.L C.P.L
      C.P.g C.P.g uC uC hdC1 hdC2 (C.act.act c) (C.act.hom c)
    refine ⟨G, hGex, ?_⟩
    obtain ⟨ht, hd1⟩ := hGdiff wv C.v hvt hwv
    have hd2 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb C.P.A C.P.L C.P.g 1 uC ![wv] ![C.v] ![τ₀ c] _
      (fun i => by fin_cases i; exact hvt) (fun i => by fin_cases i; exact hwv) (hτ₀c c)
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hd2
    exact (hdC1 _ ht).unique hd1 hd2

  set x : L → (Fin T.pol.g → ℂ) := fun a => F a wv with hxdef
  have hxd : ∀ a, uT.IsDiff (x a) (C.v ≫ ψ a) ∧ IsTangent (C.v ≫ ψ a) := fun a =>
    ⟨(hFdiff a wv C.v hvt hwv).2, (hFdiff a wv C.v hvt hwv).1⟩
  have hxadd : ∀ a b, x (a + b) = x a + x b := by
    intro a b
    have hm : C.v ≫ ψ (a + b) = (C.v ≫ ψ a) * (C.v ≫ ψ b) := by
      rw [hadd]
      exact MonObj.comp_mul _ _ _
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb T.pol.A T.pol.L T.pol.g 2 uT ![x a, x b]
      ![C.v ≫ ψ a, C.v ≫ ψ b] ![1, 1] _
      (fun i => by fin_cases i; exacts [(hxd a).2, (hxd b).2])
      (fun i => by fin_cases i; exacts [(hxd a).1, (hxd b).1])
      (GlobalTheory.CM.LieChar.isLieComb_mul (C.v ≫ ψ a) (C.v ≫ ψ b))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] at hd
    rw [← hm] at hd
    exact (hdT1 _ (hxd (a + b)).2).unique (hxd (a + b)).1 hd
  have hxrt : ∀ a, x (H.rt • a) = (2 * ω - 1) • x a := by
    intro a
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb T.pol.A T.pol.L T.pol.g 1 uT ![x a]
      ![C.v ≫ ψ a] ![2 * ω - 1] _
      (fun i => by fin_cases i; exact (hxd a).2) (fun i => by fin_cases i; exact (hxd a).1) (hrt a)
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hd
    have e : C.v ≫ ψ (H.rt • a) = C.v ≫ ψ a ≫ T.t.act.act H.rt := by rw [hlin]
    rw [← e] at hd
    exact (hdT1 _ (hxd (H.rt • a)).2).unique (hxd (H.rt • a)).1 hd
  have hω : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := char_sq ω τ₀ hτ₀
  have hxc : ∀ (c : OK H) (a : L), x ((c : 𝓞 E) • a) = τ₀ c • x a :=
    fun c a => smul_of_rt ω τ₀ hτ₀ x hxadd hxrt c a

  have hFs : ∀ a (s : ℂ), F a (s • wv) = s • x a := fun a s => by rw [map_smul]

  have hq : ∀ a : L, hermForm HT (x a) (x a) =
      (D.EF (H.w0 • (a : D.La)) a : ℂ) * ((ε : ℤ) * hermForm HC wv wv) := by
    intro a
    obtain ⟨N, hN, hiso⟩ := hpow a (Set.mem_univ a)
    have hp := GlobalTheory.hermForm_pull_eq_of_lbIso_pow C.P.A T.pol.A C.P.L T.pol.L C.P.isLB T.pol.isLB C.P.g T.pol.g
      uC uT HC χC HT χT hAHC hAHT (ψ a) (F a) (hFex a) N (N * (D.EF (H.w0 • (a : D.La)) a).natAbs) hiso wv wv
    have habs : (((D.EF (H.w0 • (a : D.La)) a).natAbs : ℕ) : ℤ) = (ε : ℤ) * D.EF (H.w0 • (a : D.La)) a := by
      by_cases ha : a = 0
      · subst ha
        simp
      · have hne : (a : D.La) ≠ 0 := fun h0 => ha (Subtype.ext h0)
        have hps := hpos (a : D.La) a.2 hne
        rw [Int.natCast_natAbs]
        rcases Int.units_eq_one_or ε with hε | hε <;> rw [hε] at hps ⊢ <;> norm_num at hps ⊢
        · first | exact hps.le | exact abs_of_pos hps | linarith
        · first | exact hps.le | exact abs_of_neg hps | linarith
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have habsC : (((D.EF (H.w0 • (a : D.La)) a).natAbs : ℕ) : ℂ) = ((ε : ℤ) : ℂ) * D.EF (H.w0 • (a : D.La)) a := by
      rw [← Int.cast_natCast (R := ℂ), habs, Int.cast_mul]
    push_cast at hp
    rw [habsC] at hp
    have : (N : ℂ) * (hermForm HT (x a) (x a) - (D.EF (H.w0 • (a : D.La)) a : ℂ) * ((ε : ℤ) * hermForm HC wv wv)) = 0 := by
      simp only [hxdef]
      linear_combination hp
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hNC)
  have hpol := fun a b => polarise D L HT ω ((ε : ℤ) * hermForm HC wv wv) hω x hxadd hxrt hq a b
  refine ⟨?_, hadd, hlin, ?_⟩
  · intro a
    refine ⟨hmon a, ?_⟩
    intro c
    have e1 : ψ a ≫ (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))).act c = ψ ((c : 𝓞 E) • a) := by
      rw [hlin]
      rfl
    rw [e1]
    apply hFuniq
    intro z
    obtain ⟨s, rfl⟩ := span z
    obtain ⟨G, hGex, hGw⟩ := hG c
    have lhs : F ((c : 𝓞 E) • a) (s • wv) = (s * τ₀ c) • x a := by rw [hFs, hxc, smul_smul]
    have rhs : F a (G (s • wv)) = (s * τ₀ c) • x a := by rw [map_smul, hGw, smul_smul, map_smul]
    rw [lhs, ← Category.assoc, ← hGex, ← hFex a, rhs]
  · intro a b
    obtain ⟨G, hGex, hGw⟩ := hG (h a b)
    have hW := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hTh hLaws C.P C.P T.pol C.P uC uC uT uC HT HC χT χC hAHT hAHC (ψ a) (ψ b)
      (C.act.act (h a b)) (𝟙 C.P.A) (F a) (F b) G LinearMap.id (hFex a) (hFex b) hGex (fun z => by simp)).mpr ?_
    · exact GlobalTheory.T.lambdaBundleIso_of_weilPairing_compatible hLaws ℂ C.P C.P T.pol C.P (ψ a) (ψ b) (C.act.act (h a b)) (𝟙 C.P.A) (hmon a) (hmon b)
        (C.act.hom _) inferInstance hW
    intro z w
    obtain ⟨s, rfl⟩ := span z
    obtain ⟨t', rfl⟩ := span w
    have e : h a b = (((ε : ℤ) * (D.EF (H.w0 • (a : D.La)) b - D.EF a b) : ℤ) : OK H) +
        (((ε : ℤ) * D.EF a b : ℤ) : OK H) * wK H := by
      apply Subtype.ext
      rw [hK]
      push_cast
      rfl
    have hh : τ₀ (h a b) = (((ε : ℤ) * (D.EF (H.w0 • (a : D.La)) b - D.EF a b) : ℤ) : ℂ) +
        (((ε : ℤ) * D.EF a b : ℤ) : ℂ) * ω := by
      rw [e, map_add, map_mul, map_intCast, map_intCast, hτ₀]
    rw [hFs, hFs, map_smul, hGw, LinearMap.id_apply, smul_smul, GlobalTheory.EigenNorm.hermForm_smul_left,
      GlobalTheory.EigenNorm.hermForm_smul_right, GlobalTheory.EigenNorm.hermForm_smul_left, GlobalTheory.EigenNorm.hermForm_smul_right,
      hpol a b, hh]
    push_cast
    ring

end GlobalTheory.CM.FamPairing
end
