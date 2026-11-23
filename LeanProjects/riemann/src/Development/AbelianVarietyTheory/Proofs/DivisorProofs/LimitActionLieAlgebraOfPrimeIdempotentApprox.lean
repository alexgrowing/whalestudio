import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LimAct

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv
open ReciprocityTheory.ChartRestriction.G.TB (dAct)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA (dActH)

theorem exists_lim {O : Type} [CommRing O] (q : O) [IsAdicComplete (Ideal.span {q}) O] (g : ℕ → O)
    (hg : ∀ m n, m ≤ n → ∃ w, g n - g m = q ^ m * w) : ∃ L : O, ∀ n, ∃ w, L - g n = q ^ n * w := by
  have key : ∀ m n, m ≤ n → g m ≡ g n [SMOD (Ideal.span {q} ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    obtain ⟨w, hw⟩ := hg m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨-w, by rw [← neg_sub, hw]; ring⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {q}) g (fun {m n} h => key m n h)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, by rw [← neg_sub, ← ha]; ring⟩

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem isIntV_alg (o : X.O) : IsIntV (vX_vp X) (algebraMap X.O X.C o) := by
  rw [GlobalTheory.FactorDepth.isIntV_iff]; exact X.ints.map_le_one o

theorem le_v_pow_mul (N : ℕ) (o : X.O) :
    ((N : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * algebraMap X.O X.C o) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p, nsmul_one]
  have h := isIntV_alg X o
  unfold IsIntV at h
  calc ((N : ℝ) : WithTop ℝ) = (N : WithTop ℝ) := by norm_cast
    _ ≤ (N : WithTop ℝ) + vX_vp X (algebraMap X.O X.C o) := le_add_of_nonneg_right h

theorem eq_zero_of_le_v (x : X.C) (h : ∀ N : ℕ, ((N : ℝ) : WithTop ℝ) ≤ vX_vp X x) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ))
  have := h N
  rw [vX_vp_apply X hx, WithTop.coe_le_coe] at this
  linarith

end Val

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [inst : StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActXH : 𝓞 E →+* Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dActH X.C Ch.ch.B

theorem dActX_eq (a : 𝓞 E) : dActX Ch X a = dActXH Ch X a := rfl

def entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) : X.O :=
  X.ι (coeff (Finsupp.single ((0 : Fin 1), e') 1) (Ch.actT a e))

theorem alg_entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    algebraMap X.O X.C (entO Ch X a e e') = dActX Ch X a e e' := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  rw [entO, ← X.comp]
  show _ = coeff _ (Ch.ch.B.actK X.C a e)
  unfold FB.actK
  rw [Ch.gen.1.2.1 a e, coeff_map, coeff_map]
  rfl

theorem dActX_apply (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    dActX Ch X a e e' = X.ιF (letI := io.toAlgebra; dAct T.Fr Ch.ch.B a e e') := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  show coeff _ (Ch.ch.B.actK X.C a e) = X.ιF (coeff _ (Ch.ch.B.actK T.Fr a e))
  unfold FB.actK
  rw [coeff_map, coeff_map]
  rfl

theorem dActX_mulVec_lieVec (hst : ∀ a : 𝓞 E, star a = H.bar a) (φ : 𝓞 E →+* T.V) (τ : E →+* ℂ)
    (hφ : ∀ a : 𝓞 E, algebraMap T.V T.Fr (φ a) = io (embK c τ a)) (a : 𝓞 E) (i : Fin (Dw.mult τ)) :
    (dActX Ch X a).mulVec (lieVec Ch X ⟨τ, i⟩) = jX X (φ a) • lieVec Ch X ⟨τ, i⟩ := by
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  letI := io.toAlgebra
  have h := GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ⟨τ, i⟩
  funext e
  have h3 := congrArg X.ιF (congrFun h e)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h3 ⊢
  simp only [dActX_apply, lieVec, jX, RingHom.comp_apply, hφ, ← Ch.gen.1.2.2.2.2.2.2]
  exact h3

end Chart

theorem cauchy_eps_mul {R V : Type} [CommRing R] [CommRing V] (φ : R →+* V) (q : R) (ε x : ℕ → R) (t : V)
    (hε : ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M})
    (hx : ∀ N : ℕ, ∃ z, φ (x N) = t + φ q ^ N * z) (m n : ℕ) (hmn : m ≤ n) :
    ∃ w, ε n * x n - ε m * x m = q ^ m * w := by
  have hstep : ∀ N, ε (N + 1) * x (N + 1) - ε N * x N ∈ Ideal.span {q ^ N} := by
    intro N
    obtain ⟨z0, hz0⟩ := hx N
    obtain ⟨z1, hz1⟩ := hx (N + 1)
    obtain ⟨u0, hu0⟩ := (hε N).1
    obtain ⟨u1, hu1⟩ := (hε (N + 1)).1
    have ha : ε N * (x (N + 1) - x N) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨φ q * z1 - z0, by rw [map_sub, hz0, hz1]; ring⟩
    have hb : ε (N + 1) * (1 - ε N) ∈ Ideal.span {q ^ N} :=
      (hε (N + 1)).2 N (Nat.le_succ N) _ ⟨-u0, by rw [map_sub, map_one, hu0]; ring⟩
    have hc : ε N * (1 - ε (N + 1)) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨-(φ q * u1), by rw [map_sub, map_one, hu1]; ring⟩
    have e : ε (N + 1) * x (N + 1) - ε N * x N =
        ε N * (x (N + 1) - x N) + (ε (N + 1) * (1 - ε N) - ε N * (1 - ε (N + 1))) * x (N + 1) := by ring
    rw [e]
    exact Ideal.add_mem _ ha (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hb hc))
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨0, by ring⟩
  | succ n hmn ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨w + q ^ k * w', by linear_combination hw - hw'⟩

end GlobalTheory.IsoTriv.LimAct

namespace GlobalTheory.IsoTriv

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv.LimAct

theorem limActSt_of_epsSt (hε : EpsSt) : LimActSt := by
  intro E _ _ _ H Dw l Xo c inst hst T io y Ch p _ X τ
  obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c τ))
  have hP : φ (p : 𝓞 E) = (p : T.V) := map_natCast φ p
  have hp0 : φ (p : 𝓞 E) ≠ 0 := by rw [hP]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpu : ¬ IsUnit (φ (p : 𝓞 E)) := by rw [hP]; exact not_isUnit_p X
  obtain ⟨ε, hεN⟩ := hε (𝓞 E) T.V φ (p : 𝓞 E) hp0 hpu
  refine ⟨ε, fun t x hx => ?_⟩
  have hxN : ∀ N : ℕ, ∃ z, φ (x N) = t + φ (p : 𝓞 E) ^ N * z := fun N => by
    obtain ⟨z, hz⟩ := hx N
    exact ⟨z, by rw [hP]; exact IsFractionRing.injective T.V T.Fr ((hφ (x N)).trans hz)⟩
  have hcau := cauchy_eps_mul φ (p : 𝓞 E) ε x t hεN hxN
  have hent : ∀ e e', ∃ L : X.O, ∀ N, ∃ w, L - entO Ch X (ε N * x N) e e' = (p : X.O) ^ N * w := by
    intro e e'
    refine exists_lim (p : X.O) (fun N => entO Ch X (ε N * x N) e e') fun m n hmn => ?_
    obtain ⟨w, hw⟩ := hcau m n hmn
    refine ⟨entO Ch X w e e', X.ints.hom_inj ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO, alg_entO, alg_entO, dActX_eq, dActX_eq, dActX_eq,
      ← Matrix.sub_apply, ← map_sub, hw, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul,
      Nat.cast_pow]
  choose L W hW using hent
  have hA : ∀ N e e', algebraMap X.O X.C (L e e') =
      dActX Ch X (ε N * x N) e e' + (p : X.C) ^ N * algebraMap X.O X.C (W e e' N) := by
    intro N e e'
    have h := congrArg (algebraMap X.O X.C) (hW e e' N)
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO] at h
    linear_combination h
  refine ⟨Matrix.of fun e e' => algebraMap X.O X.C (L e e'), fun N e e' => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply, hA N, add_sub_cancel_left]
    exact le_v_pow_mul X N _
  · funext e
    rw [← sub_eq_zero]
    refine eq_zero_of_le_v X _ fun N => ?_
    obtain ⟨z0, hz0⟩ := hxN N
    obtain ⟨u, hu⟩ := (hεN N).1
    obtain ⟨z, hz⟩ : ∃ z, φ (ε N * x N) = t + (p : T.V) ^ N * z :=
      ⟨z0 + u * t + (p : T.V) ^ N * u * z0, by rw [map_mul, hu, hz0, hP]; ring⟩
    have hj : ∀ r : T.V, jX X r = algebraMap X.O X.C (X.ι r) := fun r => X.comp r
    have he := congrFun (dActX_mulVec_lieVec Ch X hst φ τ (fun a => hφ a) (ε N * x N) i) e
    rw [hz, map_add, map_mul, map_pow, map_natCast] at he
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply] at he ⊢
    have key : ∑ e', algebraMap X.O X.C (L e e') * lieVec Ch X ⟨τ, i⟩ e' - jX X t * lieVec Ch X ⟨τ, i⟩ e =
        (p : X.C) ^ N * algebraMap X.O X.C
          (∑ e', W e e' N * X.ι (Ch.uvecT ⟨τ, i⟩ e') + X.ι z * X.ι (Ch.uvecT ⟨τ, i⟩ e)) := by
      simp only [hA N, add_mul, Finset.sum_add_distrib, he, map_add, map_sum, map_mul, ← hj, mul_add, Finset.mul_sum,
        mul_assoc]
      simp only [lieVec]
      ring
    rw [key]
    exact le_v_pow_mul X N _

end GlobalTheory.IsoTriv
