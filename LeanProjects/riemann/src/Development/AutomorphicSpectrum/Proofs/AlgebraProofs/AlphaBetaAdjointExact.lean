import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiplicationByPFactorsFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormulaStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutationStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.Isotropy

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

variable {R : Type} [CommRing R] {d : ℕ}

local notation "P₀" => pt R (n := 2) d 0
local notation "P₁" => pt R (n := 2) d 1

theorem cz_pair {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : CZ ![a, b] := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem cz_single {n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) : CZ ![a] := by
  intro j i
  fin_cases j
  exact ha i

theorem pt_noConst {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

theorem ptPow_noConst {n p : ℕ} (hp : p ≠ 0) (j : Fin n) (i : Fin d) :
    constantCoeff (ptPow R d p j i) = 0 := by
  simp [ptPow, hp]

theorem composition_no_constant_term {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) {n : ℕ} {a : Pt R n d}
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 V a i) = 0 :=
  constantCoeff_ev (cz_single ha) (hV i)

theorem ev_pow_eq {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) (k : ℕ) :
    ev a (f ^ k) = ev a f ^ k := by
  simp only [← evHom_apply ha, map_pow]

theorem ev_pair_ev {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {u v : Pt R 2 d} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (f : PS R 2 d) :
    ev ![a, b] (ev ![u, v] f) = ev ![fun i => ev ![a, b] (u i), fun i => ev ![a, b] (v i)] f := by
  rw [ev_ev (cz_pair ha hb) (cz_pair hu hv)]
  congr 1
  funext j i
  fin_cases j <;> rfl

theorem ev_first {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : (fun i => ev ![a, b] (P₀ i)) = a :=
  funext fun i => ev_X (cz_pair ha hb) 0 i

theorem ev_second {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : (fun i => ev ![a, b] (P₁ i)) = b :=
  funext fun i => ev_X (cz_pair ha hb) 1 i

theorem ev_first_pow {n : ℕ} (p : ℕ) {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev ![a, b] (ptPow R d p 0 i)) = fun i => a i ^ p :=
  funext fun i => by
    simp only [ptPow]
    rw [ev_pow_eq (cz_pair ha hb), ev_X (cz_pair ha hb)]
    rfl

theorem ev_second_pow {n : ℕ} (p : ℕ) {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev ![a, b] (ptPow R d p 1 i)) = fun i => b i ^ p :=
  funext fun i => by
    simp only [ptPow]
    rw [ev_pow_eq (cz_pair ha hb), ev_X (cz_pair ha hb)]
    rfl

theorem pt_pow_eq {n : ℕ} (p : ℕ) (j : Fin n) : (fun i => pt R (n := n) d j i ^ p) = ptPow R d p j := rfl

theorem ev_comp1_pair {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) {m n : ℕ}
    {a : Fin m → Pt R n d} (ha : CZ a) {b : Pt R m d} (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev a (comp1 V b i)) = comp1 V (fun i => ev a (b i)) := by
  funext i
  simp only [comp1]
  rw [ev_ev ha (cz_single hb)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem composition_frobenius_point {p n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) :
    comp1 (ptPow R d p 0) a = fun i => a i ^ p := by
  funext i
  simp only [comp1, ptPow]
  rw [ev_pow_eq (cz_single ha), ev_X (cz_single ha)]
  rfl

theorem composition_assoc_frobenius_point {V : Pt R 1 d} {p n : ℕ} (hp : p ≠ 0) {a : Pt R n d}
    (ha : ∀ i, constantCoeff (a i) = 0) :
    comp1 (comp1 V (ptPow R d p 0)) a = comp1 V (fun i => a i ^ p) := by
  funext i
  simp only [comp1]
  rw [ev_ev (cz_single ha) (cz_single (ptPow_noConst hp 0))]
  congr 1
  funext j l
  fin_cases j
  exact congrFun (composition_frobenius_point ha) l

theorem lin_tau {p : ℕ} (hp : p ≠ 1) : lin (ptPow R d p 0 : Pt R 1 d) 1 = 0 := by
  ext i j
  simp only [lin, ptPow, Matrix.zero_apply]
  rw [coeff_X_pow, if_neg]
  intro h
  rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨_, h⟩ | ⟨h, _⟩
  · exact hp h.symm
  · exact one_ne_zero h

theorem calc_cmp {f : PS R 2 d} (hf : AxOne f) {φ ψ : Pt R 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    AxOne (ev (n := 2) ![comp1 φ P₀, comp1 ψ P₁] f) ∧
      bil (ev (n := 2) ![comp1 φ P₀, comp1 ψ P₁] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 :=
  have t := GlobalTheory.T.formal_bilinear_term_product R d f f φ ψ hf hf hφ hψ
  ⟨t.2.2.2.1, t.2.2.2.2.1⟩

theorem comp1_identity_left {n : ℕ} (j : Fin n) : comp1 (pt R d 0) (pt R (n := n) d j) = pt R d j :=
  germ_comp1_zero_point_left _ (pt_noConst j)

theorem calc_right {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp0 : p ≠ 0) (hp : p ≠ 1) :
    AxOne (ev (n := 2) ![P₀, ptPow R d p 1] f) ∧ bil (ev (n := 2) ![P₀, ptPow R d p 1] f) 1 1 = 0 := by
  have t := calc_cmp hf (φ := pt R d 0) (ψ := ptPow R d p 0) (pt_noConst 0) (ptPow_noConst hp0 0)
  rw [comp1_identity_left, composition_frobenius_point (pt_noConst 1), pt_pow_eq, lin_tau hp, Matrix.mul_zero] at t
  exact t

theorem calc_left {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp0 : p ≠ 0) (hp : p ≠ 1) :
    AxOne (ev (n := 2) ![ptPow R d p 0, P₁] f) ∧ bil (ev (n := 2) ![ptPow R d p 0, P₁] f) 1 1 = 0 := by
  have t := calc_cmp hf (φ := ptPow R d p 0) (ψ := pt R d 0) (ptPow_noConst hp0 0) (pt_noConst 0)
  rw [comp1_identity_left, composition_frobenius_point (pt_noConst 0), pt_pow_eq, lin_tau hp, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.zero_mul] at t
  exact t

theorem calc_map_right {f : PS R 2 d} (hf : AxOne f) {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) :
    AxOne (ev (n := 2) ![P₀, comp1 V P₁] f) ∧
      bil (ev (n := 2) ![P₀, comp1 V P₁] f) 1 1 = bil f 1 1 * lin V 1 := by
  have t := calc_cmp hf (φ := pt R d 0) (ψ := V) (pt_noConst 0) hV
  rw [comp1_identity_left, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul] at t
  exact t

theorem calc_map_left {f : PS R 2 d} (hf : AxOne f) {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) :
    AxOne (ev (n := 2) ![comp1 V P₀, P₁] f) ∧
      bil (ev (n := 2) ![comp1 V P₀, P₁] f) 1 1 = (lin V 1).transpose * bil f 1 1 := by
  have t := calc_cmp hf (φ := V) (ψ := pt R d 0) hV (pt_noConst 0)
  rw [comp1_identity_left, lin_pt_eq_one, Matrix.mul_one] at t
  exact t

theorem axOne_swap {f : PS R 2 d} (hf : AxOne f) : AxOne (ev (n := 2) ![P₁, P₀] f) := by
  have c0 : ∀ i, constantCoeff ((0 : Pt R 1 d) i) = 0 := fun i => by simp
  have c1 : ∀ i, constantCoeff (pt R (n := 1) d 0 i) = 0 := pt_noConst 0
  constructor
  · rw [ev_pair_ev c0 c1 (pt_noConst 1) (pt_noConst 0), ev_first c0 c1, ev_second c0 c1]
    exact hf.2
  · rw [ev_pair_ev c1 c0 (pt_noConst 1) (pt_noConst 0), ev_first c1 c0, ev_second c1 c0]
    exact hf.1

theorem axOne_map {S : Type} [CommRing S] (φ : R →+* S) {f : PS R 2 d} (hf : AxOne f) :
    AxOne (MvPowerSeries.map φ f) := by
  have key : ∀ a : Fin 2 → Pt R 1 d, CZ a → ev a f = 1 →
      ev (fun j l => MvPowerSeries.map φ (a j l)) (MvPowerSeries.map φ f) = 1 := by
    intro a ha h
    have e : MvPowerSeries.map φ (ev a f) =
        ev (fun j l => MvPowerSeries.map φ (a j l)) (MvPowerSeries.map φ f) := by
      unfold ev
      exact map_subst ha.hasSubst f
    rw [← e, h, map_one]
  have c0 : ∀ i, constantCoeff ((0 : Pt R 1 d) i) = 0 := fun i => by simp
  have c1 : ∀ i, constantCoeff (pt R (n := 1) d 0 i) = 0 := pt_noConst 0
  constructor
  · have := key _ (cz_pair c0 c1) hf.1
    convert this using 2
    funext j l
    fin_cases j
    · simp
    · simp [pt]
  · have := key _ (cz_pair c1 c0) hf.2
    convert this using 2
    funext j l
    fin_cases j
    · simp [pt]
    · simp

theorem calc_mul {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) :
    AxOne (f * g) ∧ bil (f * g) 1 1 = bil f 1 1 + bil g 1 1 :=
  have t := GlobalTheory.T.formal_bilinear_term_product R d f g (pt R d 0) (pt R d 0) hf hg (pt_noConst 0) (pt_noConst 0)
  ⟨t.1, t.2.1 1⟩

theorem calc_swap {f : PS R 2 d} (hf : AxOne f) :
    bil (ev (n := 2) ![P₁, P₀] f) 1 1 = (bil f 1 1).transpose :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f (pt R d 0) (pt R d 0) hf hf (pt_noConst 0) (pt_noConst 0)).2.2.2.2.2.1 1 1

theorem calc_pow {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp : 1 ≤ p) :
    bil (ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] f) p p = bil f 1 1 :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f (pt R d 0) (pt R d 0) hf hf (pt_noConst 0) (pt_noConst 0)).2.2.2.2.2.2 p p hp hp

theorem bil_map_eq_zero {S : Type} [CommRing S] (φ : R →+* S) {f : PS R 2 d} (h : bil f 1 1 = 0) :
    bil (MvPowerSeries.map φ f) 1 1 = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [bil, coeff_map, Matrix.zero_apply] at this ⊢
  rw [this, map_zero]

variable {O : Type} [CommRing O] [StarRing O]

theorem am_mul_hw {p : ℕ} [Fact p.Prime] [CharP R p] (B : FB R d O) :
    am B p * hw B p = (hw B p).transpose * (bil B.sy 1 1 * hw B p + (am B p).transpose) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  obtain ⟨V, hV, hact, hlin⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B
  obtain ⟨g, hg, ha, hgb⟩ := GlobalTheory.T.pow_one_series_p_formula R p d O B
  have c0 : ∀ i, constantCoeff (P₀ i) = 0 := pt_noConst 0
  have c1 : ∀ i, constantCoeff (P₁ i) = 0 := pt_noConst 1
  have u0 : ∀ i, constantCoeff (ptPow R (n := 2) d p 0 i) = 0 := ptPow_noConst hp0 0
  have u1 : ∀ i, constantCoeff (ptPow R (n := 2) d p 1 i) = 0 := ptPow_noConst hp0 1
  have v0 := composition_no_constant_term hV c0
  have v1 := composition_no_constant_term hV c1
  have w0 := composition_no_constant_term hV u0
  have w1 := composition_no_constant_term hV u1
  have hA0 : comp1 (B.A.act (p : O)) P₀ = comp1 V (ptPow R d p 0) := by
    rw [hact, composition_assoc_frobenius_point hp0 c0, pt_pow_eq]
  have hA1 : comp1 (B.A.act (p : O)) P₁ = comp1 V (ptPow R d p 1) := by
    rw [hact, composition_assoc_frobenius_point hp0 c1, pt_pow_eq]
  have hsym : AxOne B.sy := ⟨B.symmetry_zero_fst, B.symmetry_zero_snd⟩
  have hfs : ∀ f : PS R 2 d, f ^ p = ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
      (MvPowerSeries.map (frobenius R p) f) := by
    intro f
    rw [GlobalTheory.T.power_series_pow_p_frobenius R p d 2 f]
    congr 1
    funext j
    fin_cases j <;> rfl

  obtain ⟨sy', hsy'⟩ : ∃ s, s = ev (n := 2) ![P₁, P₀] B.sy := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s, s = ev (n := 2) ![P₀, comp1 V P₁] B.sy := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ s, s = ev (n := 2) ![P₁, P₀] g := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ s, s = ev (n := 2) ![ptPow R d p 0, P₁] (MvPowerSeries.map (frobenius R p) sy') :=
    ⟨_, rfl⟩
  have axs2 : AxOne s2 := hs2 ▸ (calc_map_right hsym hV).1
  have bs2 : bil s2 1 1 = bil B.sy 1 1 * hw B p := by rw [hs2, (calc_map_right hsym hV).2, hlin]
  have axg1 : AxOne g1 := hg1 ▸ axOne_swap hg
  have bg1 : bil g1 1 1 = (am B p).transpose := by rw [hg1, calc_swap hg, hgb]
  have axsy' : AxOne (MvPowerSeries.map (frobenius R p) sy') :=
    axOne_map _ (hsy' ▸ axOne_swap hsym)
  have axt : AxOne t := ht ▸ (calc_left axsy' hp0 hp1).1
  have bt : bil t 1 1 = 0 := ht ▸ (calc_left axsy' hp0 hp1).2
  obtain ⟨g', hg'⟩ : ∃ s, s = s2 * g1 * t := ⟨_, rfl⟩
  have axg' : AxOne g' := hg' ▸ (calc_mul (calc_mul axs2 axg1).1 axt).1
  have bg' : bil g' 1 1 = bil B.sy 1 1 * hw B p + (am B p).transpose := by
    rw [hg', (calc_mul (calc_mul axs2 axg1).1 axt).2, (calc_mul axs2 axg1).2, bs2, bg1, bt, add_zero]
  have cQ := cz_pair c0 u1
  have hb : pow2 B p = ev (n := 2) ![P₀, ptPow R d p 1] g' := by
    have e1 := GlobalTheory.T.pow_two_symplectic_relation R d O B p
    have f1 : ev (n := 2) ![P₀, comp1 (B.A.act (p : O)) P₁] B.sy =
        ev (n := 2) ![P₀, ptPow R d p 1] s2 := by
      rw [hA1, hs2, ev_pair_ev c0 u1 c0 v1, ev_first c0 u1, ev_comp1_pair hV cQ c1, ev_second c0 u1]
    have f2 : ev (n := 2) ![P₁, P₀] (pow1 B p) = ev (n := 2) ![P₀, ptPow R d p 1] g1 := by
      rw [ha, hg1, ev_pair_ev c1 c0 u0 c1, ev_first_pow p c1 c0, ev_second c1 c0, pt_pow_eq,
        ev_pair_ev c0 u1 c1 c0, ev_first c0 u1, ev_second c0 u1]
    have f3 : sy' ^ p = ev (n := 2) ![P₀, ptPow R d p 1] t := by
      rw [hfs, ht, ev_pair_ev c0 u1 u0 c1, ev_first_pow p c0 u1, ev_second c0 u1, pt_pow_eq]
    have f4 : B.sy ^ p * sy' ^ p = 1 := by rw [← mul_pow, hsy', B.sy_inv, one_pow]
    calc pow2 B p = pow2 B p * (B.sy ^ p * sy' ^ p) := by rw [f4, mul_one]
      _ = pow2 B p * B.sy ^ p * sy' ^ p := (mul_assoc _ _ _).symm
      _ = ev (n := 2) ![P₀, ptPow R d p 1] s2 * ev (n := 2) ![P₀, ptPow R d p 1] g1 *
          ev (n := 2) ![P₀, ptPow R d p 1] t := by rw [e1, f1, f2, f3]
      _ = ev (n := 2) ![P₀, ptPow R d p 1] g' := by rw [hg', ev_mul cQ, ev_mul cQ]

  obtain ⟨g2, hg2⟩ : ∃ s, s = ev (n := 2) ![P₀, comp1 V P₁] g := ⟨_, rfl⟩
  obtain ⟨g3, hg3⟩ : ∃ s, s = ev (n := 2) ![comp1 V P₀, P₁] g' := ⟨_, rfl⟩
  have axg2 : AxOne g2 := hg2 ▸ (calc_map_right hg hV).1
  have bg2 : bil g2 1 1 = am B p * hw B p := by rw [hg2, (calc_map_right hg hV).2, hgb, hlin]
  have axg3 : AxOne g3 := hg3 ▸ (calc_map_left axg' hV).1
  have bg3 : bil g3 1 1 = (hw B p).transpose * (bil B.sy 1 1 * hw B p + (am B p).transpose) := by
    rw [hg3, (calc_map_left axg' hV).2, hlin, bg']
  have cP := cz_pair u0 u1
  have h1 : ev (n := 2) ![P₀, comp1 (B.A.act (p : O)) P₁] (pow1 B p) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] g2 := by
    rw [hA1, ha, hg2, ev_pair_ev c0 w1 u0 c1, ev_first_pow p c0 w1, ev_second c0 w1, pt_pow_eq,
      ev_pair_ev u0 u1 c0 v1, ev_first u0 u1, ev_comp1_pair hV cP c1, ev_second u0 u1]
  have h2 : ev (n := 2) ![comp1 (B.A.act (p : O)) P₀, P₁] (pow2 B p) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] g3 := by
    rw [hA0, hb, hg3, ev_pair_ev w0 c1 c0 u1, ev_first w0 c1, ev_second_pow p w0 c1, pt_pow_eq,
      ev_pair_ev u0 u1 v0 c1, ev_comp1_pair hV cP c0, ev_first u0 u1, ev_second u0 u1]
  have hmain : ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
        (MvPowerSeries.map (frobenius R p) (pow2 B p) * g2) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
        (MvPowerSeries.map (frobenius R p) (pow1 B p) * g3) := by
    rw [ev_mul cP, ev_mul cP, ← hfs, ← hfs, ← h1, ← h2]
    exact GlobalTheory.T.pow_one_pow_two_commutation R d O B p p

  have axb : AxOne (pow2 B p) := hb ▸ (calc_right axg' hp0 hp1).1
  have bb : bil (pow2 B p) 1 1 = 0 := hb ▸ (calc_right axg' hp0 hp1).2
  have axa : AxOne (pow1 B p) := ha ▸ (calc_left hg hp0 hp1).1
  have ba : bil (pow1 B p) 1 1 = 0 := ha ▸ (calc_left hg hp0 hp1).2
  have axfb := axOne_map (frobenius R p) axb
  have axfa := axOne_map (frobenius R p) axa
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp0
  have hco := congrArg (fun f => bil f p p) hmain
  rw [calc_pow (calc_mul axfb axg2).1 hp, calc_pow (calc_mul axfa axg3).1 hp, (calc_mul axfb axg2).2,
    (calc_mul axfa axg3).2, bil_map_eq_zero _ bb, bil_map_eq_zero _ ba, zero_add, zero_add, bg2, bg3] at hco
  exact hco

theorem beta_comp_alpha : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type)
    [CommRing O] [StarRing O] (B : FB R d O),
    (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  intro R _ p _ _ d O _ _ B
  refine ⟨fun u y => dotProduct_beta B p u y, LinearMap.ext fun u => ?_⟩
  have h : (hw B p).transpose * (am B p).transpose - am B p * hw B p +
      (hw B p).transpose * bil B.sy 1 1 * hw B p = 0 := by
    rw [am_mul_hw, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [LinearMap.comp_apply, beta_alpha_apply, h, Matrix.zero_mulVec]
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj.Isotropy
