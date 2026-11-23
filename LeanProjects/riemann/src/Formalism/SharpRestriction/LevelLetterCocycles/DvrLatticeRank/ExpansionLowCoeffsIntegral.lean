import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PolyExpand
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP

noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation PowerSeries

theorem ps_div {O : Type*} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (r : O) (k : ℕ)
    (hk : 0 < k) (hr : r ^ k ∈ I) (g : PowerSeries O) :
    ∃ (o : O) (g' : PowerSeries O), g = C o + (X - C r) * g' := by
  have hI : I ≠ ⊤ := by
    intro h
    have hH : IsHausdorff I O := inferInstance
    rw [h] at hH
    exact not_subsingleton O hH.subsingleton
  have H : (Polynomial.X ^ k - Polynomial.C (r ^ k) : Polynomial O).IsDistinguishedAt I := by
    refine ⟨⟨fun {i} hi => ?_⟩, Polynomial.monic_X_pow_sub_C _ hk.ne'⟩
    rw [Polynomial.natDegree_X_pow_sub_C] at hi
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, Polynomial.coeff_C]
    split_ifs
    · simpa using hr
    · simp
  have e := ((H.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod g).eq_mul_add
  obtain ⟨q, R, e⟩ : ∃ (q : PowerSeries O) (R : Polynomial O),
      g = ((Polynomial.X ^ k - Polynomial.C (r ^ k) : Polynomial O) : PowerSeries O) * q + R := ⟨_, _, e⟩
  obtain ⟨D', hD'⟩ : (X - C r : PowerSeries O) ∣ X ^ k - C r ^ k := sub_dvd_pow_sub_pow _ _ _
  obtain ⟨R', hR'⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := R)
  have h1 := congrArg (fun p : Polynomial O => (p : PowerSeries O)) hR'
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] at h1
  rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_pow, hD'] at e
  exact ⟨R.eval r, D' * q + R', by rw [e]; linear_combination h1⟩

theorem dvd_zeta {O : Type*} [CommRing O] [IsDomain O] (p : ℕ) (hp : p.Prime) (z : O) (hz : z ^ p = 1)
    (hz1 : z ≠ 1) : (p : O) ∣ (z - 1) ^ (p - 1) := by
  obtain ⟨t, ht⟩ := exists_add_pow_prime_eq hp (z - 1) (1 : O)
  rw [sub_add_cancel, hz, one_pow] at ht
  have hx : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  refine ⟨-t, mul_left_cancel₀ hx ?_⟩
  have : (z - 1) ^ p = (z - 1) * (z - 1) ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.pos; omega
  rw [← this]
  linear_combination -ht

section Ring

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_congr (c : ZMod n) (ζ : LL) {a b : LetA O n} (h : a c = b c) : W.lev c ζ a = W.lev c ζ b := by
  have := W.lev_letter c ζ (a - b) (by rw [Pi.sub_apply, h, sub_self])
  rwa [map_sub, sub_eq_zero] at this

theorem lev_alg (c : ZMod n) (ζ : LL) (o : O) :
    W.lev c ζ (algebraMap O (LetA O n) o) = C (algebraMap O LL o) := by
  rw [AlgHom.commutes, PowerSeries.algebraMap_apply]

theorem alg_apply (o : O) (c : ZMod n) : (algebraMap O (LetA O n) o) c = C o := by
  show algebraMap O (PowerSeries O) o = C o
  rw [PowerSeries.algebraMap_apply]; rfl

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  rw [lev_congr W c ζ (b := 1) (by simp [letE]), map_one]

theorem levπ01 (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    constantCoeff (W.lev c ζ letπ) = ζ - 1 ∧ coeff 1 (W.lev c ζ letπ) = ζ ∧
      (ζ - 1) * coeff 1 (W.lev c ζ W.q) = PD.p ∧ constantCoeff (W.lev c ζ W.q) = 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have h0 : constantCoeff (W.lev c ζ letπ) = ζ - 1 := by
    have h := congrArg constantCoeff hE
    rw [map_add, map_one, map_mul, constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hE1 : coeff 1 E = 1 := by
    have h1 := congrArg (coeff 0) hEd
    rw [PowerSeries.coeff_derivative] at h1
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_constantCoeff_apply, hE0] at h1
    simpa using h1
  obtain ⟨u, hu, -⟩ := framepf_lev_q_simple W c ζ hζ
  have hq0 : constantCoeff (W.lev c ζ W.q) = 0 := by rw [hu]; simp
  refine ⟨h0, ?_, ?_, hq0⟩
  · have h := congrArg (coeff 1) hE
    rw [map_add, coeff_C_mul, hE1, mul_one, coeff_one, if_neg one_ne_zero, zero_add] at h
    exact h
  · have hπq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simp only [letπ, LocWach.q, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
      exact W.q₀_def
    have hl := congrArg (W.lev c ζ) hπq
    rw [map_mul, map_sub, map_pow, map_add, map_one] at hl
    rw [hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul] at hl
    obtain ⟨w, hw, hw0⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
    rw [hw] at hl
    have h := congrArg (coeff 1) hl
    rw [coeff_one_mul, hq0, h0, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hw0] at h
    linear_combination h

def yR (π' : LetA O n) (c : ZMod n) (r : O) (ζ : LL) : PowerSeries LL :=
  W.lev c ζ π' - C (algebraMap O LL r)

def evA (c : ZMod n) (ζ : LL) (a : ↥W.AΔ) : PowerSeries LL := W.lev c ζ (a : LetA O n)

theorem Eat_mem {π' : LetA O n} (hπ : π' ∈ W.AΔ) (E : ZMod n → Polynomial O) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ W.AΔ := by
  intro δ hδ
  funext i
  show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
  rw [← Polynomial.aeval_algHom_apply]
  exact congrArg (fun p => Polynomial.aeval p (E i)) (congrFun (hπ δ hδ) i)

theorem lev_Eat (π' : LetA O n) (E : ZMod n → Polynomial O) (c : ZMod n) (ζ : LL) :
    W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Polynomial.aeval (W.lev c ζ π') (E c) := by
  rw [Polynomial.aeval_algHom_apply]
  apply lev_congr
  exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) c) π' (E c))

theorem cc_aeval (f : PowerSeries LL) (r : O) (hf : constantCoeff f = algebraMap O LL r)
    (P : Polynomial O) : constantCoeff (Polynomial.aeval f P) = algebraMap O LL (P.eval r) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, map_mul, map_pow, hf,
      PowerSeries.algebraMap_apply, constantCoeff_C, map_mul, map_pow]

theorem aeval_lin (π' : LetA O n) (c : ZMod n) (r : O) (ζ : LL) :
    Polynomial.aeval (W.lev c ζ π') (Polynomial.X - Polynomial.C r) = yR W π' c r ζ := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, PowerSeries.algebraMap_apply]
  rfl

variable [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
  [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] {s' : ℕ} {π' : LetA O n}
  {E : ZMod n → Polynomial O} (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 2 s' π' E) (hs : 2 * s' = PD.p - 1)
  (hs1 : 1 ≤ s') (c : ZMod n)

include hinj in
theorem z_dvd {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ) :
    (PD.p : O) ∣ (z - 1) ^ (PD.p - 1) :=
  dvd_zeta PD.p PD.hp z (hinj (by rw [map_pow, hz, map_one, hζ.pow_eq_one]))
    (fun h => hζ.ne_one PD.hp.one_lt (by rw [← hz, h, map_one]))

include hinj in

theorem expansion_low_coeffs_integral {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ)
    (a : LetA O n) : ∃ o₀ o₁ : O, constantCoeff (W.lev c ζ a) = algebraMap O LL o₀ ∧
      coeff 1 (W.lev c ζ a) = algebraMap O LL o₁ := by
  have hx : (z - 1) ^ (PD.p - 1) ∈ Ideal.span {((PD.p : ℕ) : O)} :=
    Ideal.mem_span_singleton.2 (z_dvd hinj hζ hz)
  have hk : 0 < PD.p - 1 := by have := PD.hp.one_lt; omega
  obtain ⟨o₀, g₁, h₁⟩ := ps_div _ (z - 1) _ hk hx (a c)
  obtain ⟨o₁, g₂, h₂⟩ := ps_div _ (z - 1) _ hk hx g₁
  obtain ⟨h0, h1, -, -⟩ := levπ01 W c ζ hζ
  have e : W.lev c ζ a = W.lev c ζ (algebraMap O (LetA O n) o₀ + (letπ - algebraMap O (LetA O n) (z - 1)) *
      (algebraMap O (LetA O n) o₁ + (letπ - algebraMap O (LetA O n) (z - 1)) * fun _ => g₂)) := by
    apply lev_congr
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, alg_apply, letπ]
    rw [h₁, h₂]
  set y := W.lev c ζ letπ - C (algebraMap O LL (z - 1)) with hy
  have hy0 : constantCoeff y = 0 := by
    rw [hy, map_sub, h0, constantCoeff_C, map_sub, hz, map_one, sub_self]
  have hy1 : coeff 1 y = ζ := by
    rw [hy, map_sub, h1, coeff_C, if_neg one_ne_zero, sub_zero]
  simp only [map_add, map_mul, map_sub (W.lev c ζ), lev_alg] at e
  rw [← hy] at e
  refine ⟨o₀, o₁ * z, ?_, ?_⟩
  · rw [e, map_add, map_mul, hy0, zero_mul, add_zero, constantCoeff_C]
  · rw [e, map_add, coeff_C, if_neg one_ne_zero, zero_add, coeff_one_mul, hy0, hy1, map_add, map_mul,
      hy0, constantCoeff_C, map_mul, hz]
    ring

include hinj hp9 hs in

theorem root {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ) :
    ∃ r : O, constantCoeff (W.lev c ζ π') = algebraMap O LL r ∧ (PD.p : O) ∣ r ^ 2 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨o₀, -, h₀, -⟩ := expansion_low_coeffs_integral W hinj c hζ hz (w : LetA O n)
  refine ⟨o₀ * (z - 1) ^ s', ?_, ?_⟩
  · rw [hw, map_mul, map_pow, map_mul, map_pow, h₀, (levπ01 W c ζ hζ).1, map_mul, map_pow, map_sub, hz,
      map_one]
  · rw [mul_pow, ← pow_mul, mul_comm s', hs]
    exact Dvd.dvd.mul_left (z_dvd hinj hζ hz) _

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hp9 hs1 in
theorem cc_π' (i : ZMod n) : constantCoeff (π' i) = 0 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]

include hp9 hs1 in

theorem dv {r : O} (hr : (PD.p : O) ∣ r ^ 2) : Dv (evA W c) O (yR W π' c r) := by
  intro a
  have hπ0 := cc_π' W hp9 hs1
  obtain ⟨hπΔ, hR, -⟩ := hp9
  obtain ⟨F, hF, -⟩ := hR a a.2
  obtain ⟨o, g', hg⟩ := ps_div _ r 2 two_pos (Ideal.mem_span_singleton.2 hr) (F c)
  have ha : (fun j => PowerSeries.subst (π' j) g') ∈ W.AΔ := by
    intro δ hδ
    funext j
    show W.γ₀ δ (PowerSeries.subst (π' j) g') = _
    rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 j)]
    exact congrArg (fun p => PowerSeries.subst p g') (congrFun (hπΔ δ hδ) j)
  refine ⟨o, ⟨_, ha⟩, fun ζ => ?_⟩
  unfold evA yR
  rw [← lev_alg W c ζ, ← lev_alg W c ζ, ← map_sub, ← map_mul, ← map_add]
  apply lev_congr
  have hS : PowerSeries.HasSubst (π' c) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 c)
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, alg_apply]
  rw [hF c, hg, PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_sub hS,
    PowerSeries.subst_X hS, PowerSeries.subst_C, PowerSeries.subst_C]
  rfl

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hinj hp9 in
theorem is_root {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {r : O}
    (hr : constantCoeff (W.lev c ζ π') = algebraMap O LL r) : (E c).eval r = 0 := by
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨e₁, he, -⟩ := u3downPf_lev_E W c ζ hζ _ w hw
  apply hinj
  rw [← cc_aeval _ r hr, ← lev_Eat, he, map_zero]
  simp

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hinj hp9 in

theorem simple {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {r : O}
    (hr : constantCoeff (W.lev c ζ π') = algebraMap O LL r) :
    ∃ u, yR W π' c r ζ = X * u ∧ IsUnit u := by
  obtain ⟨E₁, hE₁⟩ := Polynomial.dvd_iff_isRoot.2 (is_root W hinj hp9 c hζ hr)
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨e₁, he, he₁⟩ := u3downPf_lev_E W c ζ hζ _ w hw
  obtain ⟨u, hu⟩ : X ∣ yR W π' c r ζ := by
    rw [X_dvd_iff, yR, map_sub, hr, constantCoeff_C, sub_self]
  refine ⟨u, hu, ?_⟩
  rw [lev_Eat, hE₁, map_mul, aeval_lin, hu, mul_assoc] at he
  have h2 := mul_left_cancel₀ X_ne_zero he
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  intro h0
  apply he₁
  rw [← h2, map_mul, h0, zero_mul]

include hinj hp9 hs hs1 in

theorem fact2 {ζU ζD : LL} (hU : IsPrimitiveRoot ζU PD.p) (hD : IsPrimitiveRoot ζD PD.p) {z : O}
    (hz : algebraMap O LL z = ζU) {rU rD : O}
    (hrU : constantCoeff (W.lev c ζU π') = algebraMap O LL rU) (hpU : (PD.p : O) ∣ rU ^ 2)
    (hrD : constantCoeff (W.lev c ζD π') = algebraMap O LL rD) (hpD : (PD.p : O) ∣ rD ^ 2)
    (hne : rU ≠ rD) (hp0 : (PD.p : O) ≠ 0) :
    ∃ a₂ : O, IsUnit a₂ ∧ (∀ ζ, W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') =
      C (algebraMap O LL a₂) * yR W π' c rU ζ * yR W π' c rD ζ) ∧ (rD - rU) ^ 2 ∣ (PD.p : O) := by
  have hπ0 := cc_π' W hp9 hs1 c
  obtain ⟨E₁, hE₁⟩ := Polynomial.dvd_iff_isRoot.2 (is_root W hinj hp9 c hU hrU)
  have hD1 : E₁.IsRoot rD := by
    have := is_root W hinj hp9 c hD hrD
    rw [hE₁, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  obtain ⟨E₂, hE₂⟩ := Polynomial.dvd_iff_isRoot.2 hD1
  obtain ⟨-, -, ⟨w, hw⟩, hdeg, ⟨w', hw'⟩, -⟩ := hp9
  have hd := hdeg c
  have hE20 : E₂ ≠ 0 := by
    intro h; rw [hE₁, hE₂, h, mul_zero, mul_zero] at hd; simp at hd
  rw [hE₁, hE₂, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hE20),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hE20, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C] at hd
  obtain ⟨a₂, ha₂⟩ := Polynomial.natDegree_eq_zero.1 (show E₂.natDegree = 0 by omega)
  have hfac : ∀ ζ, W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') =
      C (algebraMap O LL a₂) * yR W π' c rU ζ * yR W π' c rD ζ := by
    intro ζ
    rw [lev_Eat, hE₁, hE₂, ← ha₂, map_mul, map_mul, aeval_lin, aeval_lin, Polynomial.aeval_C,
      PowerSeries.algebraMap_apply]
    ring
  refine ⟨a₂, ?_, hfac, ?_⟩
  · have h1 := congrArg constantCoeff (congrFun hw' c)
    have h2 : constantCoeff (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c) = rU * rD * a₂ := by
      show constantCoeff (Polynomial.aeval (π' c) (E c)) = _
      rw [hE₁, hE₂, ← ha₂]
      simp [hπ0, PowerSeries.algebraMap_apply]
      ring
    have h3 : constantCoeff (W.q c) = (PD.p : O) := Formalism.MainNotions.N.Ln34.CrystallineExponents.constantCoeff_q_zero_eq_p W
    rw [Pi.mul_apply, map_mul, h2, h3] at h1
    obtain ⟨tU, htU⟩ := hpU
    obtain ⟨tD, htD⟩ := hpD
    have h4 : (PD.p : O) ^ 2 * (a₂ * (a₂ * constantCoeff ((w' : LetA O n) c) ^ 2 * tU * tD)) =
        (PD.p : O) ^ 2 * 1 := by
      conv_rhs => rw [h1]
      rw [mul_pow, mul_pow, mul_pow, htU, htD]; ring
    exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ (pow_ne_zero 2 hp0) h4)
  · obtain ⟨h0, h1, hq1, -⟩ := levπ01 W c ζU hU
    obtain ⟨o₀, o₁, ho₀, ho₁⟩ := expansion_low_coeffs_integral W hinj c hU hz (w : LetA O n)
    obtain ⟨o₀', -, ho₀', -⟩ := expansion_low_coeffs_integral W hinj c hU hz (w' : LetA O n)
    have sectionFrameQuotient : constantCoeff (yR W π' c rU ζU) = 0 := by
      rw [yR, map_sub, hrU, constantCoeff_C, sub_self]
    have hyD0 : constantCoeff (yR W π' c rD ζU) = algebraMap O LL (rU - rD) := by
      rw [yR, map_sub, hrU, constantCoeff_C, map_sub]
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s' = s₀ + 1 := ⟨s' - 1, by omega⟩
    have hyU1 : coeff 1 (yR W π' c rU ζU) =
        (ζU - 1) ^ s₀ * algebraMap O LL (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z) := by
      rw [yR, map_sub, coeff_C, if_neg one_ne_zero, sub_zero, hw, map_mul, map_pow, coeff_one_mul,
        coeff_one_pow, map_pow, h0, h1, ho₀, ho₁]
      simp only [map_add, map_mul, map_sub, hz, map_one, map_natCast, Nat.add_sub_cancel]
      ring
    rw [hw', map_mul, hfac] at hq1
    simp only [coeff_one_mul, map_mul, sectionFrameQuotient, hyD0, hyU1, ho₀', constantCoeff_C, coeff_C,
      if_neg one_ne_zero] at hq1
    have h5 : (PD.p : O) = (z - 1) ^ (s₀ + 1) * (rD - rU) *
        (-(o₀' * a₂ * (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z))) := by
      apply hinj
      rw [map_natCast, ← hq1]
      simp only [map_add, map_mul, map_sub, hz, map_one, map_natCast, map_pow, map_neg]
      ring
    obtain ⟨t, ht⟩ := z_dvd hinj hU hz
    rw [← hs] at ht
    set Ω := -(o₀' * a₂ * (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z))
    refine ⟨t * Ω ^ 2, mul_left_cancel₀ hp0 ?_⟩
    have : (PD.p : O) * (PD.p : O) = ((z - 1) ^ (s₀ + 1) * (rD - rU) * Ω) ^ 2 := by
      rw [← h5]; ring
    rw [this, mul_pow, mul_pow, ← pow_mul, mul_comm (s₀ + 1), ht]
    ring

end Ring

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
