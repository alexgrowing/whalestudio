import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroDoubleMultiplicationPair
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfLinear

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MaximalIdealCongruence RowTiePE0 RowTiePProj RowTiePLSmall

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem coeff_aOf (Y : FBChart C V O dd) (u : Fin dd → C) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (Y.aOf u) = ∑ i, u i ^ V.l * MvPowerSeries.coeff
      (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1 := rfl

theorem aLin_mul_left (Y : FBChart C V O dd) (c : C) (u v : Fin dd → C) :
    Y.aLin (fun i => c * u i) v = c ^ V.l * Y.aLin u v := by
  unfold FBChart.aLin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_aOf, coeff_aOf, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

theorem aLin_mul_right (Y : FBChart C V O dd) (c : C) (u v : Fin dd → C) :
    Y.aLin u (fun i => c * v i) = c * Y.aLin u v := by
  unfold FBChart.aLin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aLin_sum_right (Y : FBChart C V O dd) {ι : Type} [Fintype ι] (u : Fin dd → C) (b : ι → C)
    (e : ι → Fin dd → C) : Y.aLin u (∑ c, b c • e c) = ∑ c, b c * Y.aLin u (e c) := by
  unfold FBChart.aLin
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aLin_int (Y : FBChart C V O dd) {u v : Fin dd → C} (hu : ∀ i, V.Ge 0 (u i)) (hv : ∀ i, V.Ge 0 (v i)) :
    V.Ge 0 (Y.aLin u v) :=
  VF.Ge.sum fun j _ => (hv j).mul_int (intS_aOf Y (first_unit_series_integral C V O dd Y) u hu _)

theorem mm_of_unit_mul {c x : C} (hc : V.v c = 0) (h : V.MM (c * x)) : V.MM x := by
  unfold VF.MM at *
  rwa [V.v.map_mul, hc, zero_add] at h

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) : V.MM (A ^ V.l - B ^ V.l) := by
  have h1 := mm_add_pow (V := V) hB (hA.sub hB)
  have h2 : V.MM ((A - B) ^ V.l) := mm_pow h V.l_prime.ne_zero
  have e : A ^ V.l - B ^ V.l = ((B + (A - B)) ^ V.l - B ^ V.l - (A - B) ^ V.l) + (A - B) ^ V.l := by
    rw [add_sub_cancel]; ring
  rw [e]
  exact mm_add h1 h2

section Self

variable {d : ℕ} {I0 : Type} [Fintype I0]

theorem gm_frob (Y : FBChart C V O dd) (p : SelfData Y d I0) (a : ZMod d) (r s : Fin 2) :
    V.MM (p.gm (a + 1) r s - p.gm a r s ^ V.l) := by
  obtain ⟨M, hM⟩ := p.gm_lim 1
  have h0 := hM a r s
  have h1 := hM (a + 1) r s
  rw [Nat.cast_one] at h0 h1
  have e : p.gm (a + 1) r s - p.gm a r s ^ V.l =
      (p.gm (a + 1) r s - p.em (a + 1) (M r s)) + (p.em (a + 1) (M r s) - p.em a (M r s) ^ V.l) -
        (p.gm a r s ^ V.l - p.em a (M r s) ^ V.l) := by ring
  rw [e]
  exact mm_sub (mm_add (maximal_of_valuation_ge_one h1) (p.em_frob a _))
    (mm_pow_sub (SelfData.gm_int Y p a r s) (p.em_int a _) (maximal_of_valuation_ge_one h0))

end Self

theorem adj_seq (hAdj : ALinAdjSt) (Y : FBChart C V O dd) (s : ℕ → O) (h1 : ActCv Y s)
    (h2 : ActCv Y (fun n => star (s n))) :
    ∃ e eb : Pt C 1 dd,
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (eb i) - MvPowerSeries.coeff μ (Y.B.A.act (star (s n)) i))) ∧
      (∀ i, IntS V (eb i)) ∧
      ∀ u : Fin dd → C, (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
        V.MM (Y.aLin (linAct e u) v - Y.aLin u (linAct eb v)) := by
  obtain ⟨e, eb, hi, hib, he, heb, hhom, hexp⟩ := endomorphism_limit_integral Y s h1 h2
  refine ⟨e, eb, he, heb, hib, ?_⟩
  exact hAdj C V O dd Y e eb hi hib (const_of_lim Y (tends_of_endomorphism_limit Y he))
    (const_of_lim Y (a := fun n => star (s n)) (tends_of_endomorphism_limit Y (a := fun n => star (s n)) heb)) hhom hexp

theorem linAct_of_lim (Y : FBChart C V O dd) {s : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i)))
    {u : Fin dd → C} {χ : ℕ → C} {c : C} (hu : ∀ n, linAct (Y.B.A.act (s n)) u = χ n • u) (hχ : Tends V χ c) :
    linAct e u = c • u := by
  funext i
  have L := linAct_tends (tends_of_endomorphism_limit Y he) u i
  have eq : (fun n => linAct (Y.B.A.act (s n)) u i) = fun n => χ n * u i := funext fun n => by
    rw [hu]; rfl
  rw [eq] at L
  exact L.unique (hχ.mul (tends_const _))

theorem actCv_const (Y : FBChart C V O dd) (β : O) : ActCv Y (fun _ => β) := fun N _ _ =>
  ⟨0, fun _ _ => by rw [sub_self]; exact VF.Ge.zero _⟩

theorem linAct_int {φ : Pt C 1 dd} (hφ : ∀ i, IntS V (φ i)) {v : Fin dd → C} (hv : ∀ i, V.Ge 0 (v i)) (i : Fin dd) :
    V.Ge 0 (linAct φ v i) :=
  VF.Ge.sum fun j _ => (hφ i _).mul_int (hv j)

section Self2

variable {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0]

theorem orth (hAdj : ALinAdjSt) (Y : FBChart C V O dd) (p : SelfData Y d I0) (a0 : ZMod d) (u0 : Fin dd → C)
    (hu0 : ∀ i, V.Ge 0 (u0 i)) (heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) (hV1 : Y.FirstVanishingAt u0)
    (q : I0) (hq : a0 + 1 ≠ p.ty0 q + p.hd) : V.MM (Y.aLin u0 (p.e q)) := by
  obtain ⟨β, hβ⟩ := p.em_sep (a0 + 1) (p.ty0 q + p.hd) hq
  obtain ⟨e, eb, he, heb, -, hadj⟩ := adj_seq hAdj Y (fun _ => β) (actCv_const Y β) (actCv_const Y (star β))
  have e1 : linAct e u0 = p.em a0 β • u0 := linAct_of_lim Y he (fun _ => heig β) (tends_const _)
  have e2 : linAct eb (p.e q) = p.em (p.ty0 q + p.hd) β • p.e q :=
    linAct_of_lim Y (s := fun _ => star β) heb (fun _ => by rw [p.e_eig, p.em_conj]) (tends_const _)
  have h := hadj u0 hu0 hV1 (p.e q) (p.e_int q)
  rw [e1, e2] at h
  have f1 : Y.aLin (p.em a0 β • u0) (p.e q) = p.em a0 β ^ V.l * Y.aLin u0 (p.e q) :=
    aLin_mul_left Y (p.em a0 β) u0 (p.e q)
  have f2 : Y.aLin u0 (p.em (p.ty0 q + p.hd) β • p.e q) = p.em (p.ty0 q + p.hd) β * Y.aLin u0 (p.e q) :=
    aLin_mul_right Y _ u0 (p.e q)
  rw [f1, f2] at h
  have hL := aLin_int Y hu0 (p.e_int q)
  refine mm_of_unit_mul hβ ?_
  have e3 : (p.em (a0 + 1) β - p.em (p.ty0 q + p.hd) β) * Y.aLin u0 (p.e q) =
      (p.em (a0 + 1) β - p.em a0 β ^ V.l) * Y.aLin u0 (p.e q) +
        (p.em a0 β ^ V.l * Y.aLin u0 (p.e q) - p.em (p.ty0 q + p.hd) β * Y.aLin u0 (p.e q)) := by ring
  rw [e3]
  exact mm_add (mm_mul_ge (p.em_frob a0 β) hL) h

theorem onType (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C)
    (hu0 : ∀ i, V.Ge 0 (u0 i)) (q : I0) (hq : a0 + 1 = p.ty0 q + p.hd)
    (hc0 : V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i) (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) :
    V.MM (Y.aLin u0 (p.e q)) := by
  have hty : p.ty0 q = a0 + 1 + p.hd := by
    rw [hq, add_assoc, p.hd_two, add_zero]
  have hL := aLin_int Y hu0 (p.e_int q)
  have e1 : ∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i) (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i) =
      (∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [aLin_mul_left, aLin_mul_right, hty]
    ring
  rw [e1] at hc0
  have hS : V.MM (1 - ∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) := by
    rw [← SelfData.gm_pair Y p (a0 + 1) g, ← Finset.sum_sub_distrib]
    refine mm_sum _ _ fun col _ => ?_
    rw [← sub_mul]
    exact mm_mul_ge (gm_frob Y p a0 col g) (SelfData.gm_int Y p _ _ _)
  have e2 : Y.aLin u0 (p.e q) =
      (1 - ∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) +
        (∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) := by ring
  rw [e2]
  exact mm_add (mm_mul_ge hS hL) hc0

end Self2

end SelfLinear

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MaximalIdealCongruence RowTiePE0 RowTiePProj RowTiePLSmall SelfLinear in

theorem noLin_self (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) {C : Type} [Field C] [CharZero C] {V : VF C}
    {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C) (hu0 : ∀ i, V.Ge 0 (u0 i))
    (heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) (hV1 : Y.FirstVanishingAt u0)
    (hc0 : ∀ q : I0, V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i)
      (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) :
    ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) → V.MM (Y.aLin u0 v) := by
  intro v hv
  have hq : ∀ q, V.MM (Y.aLin u0 (p.e q)) := fun q => by
    by_cases h : a0 + 1 = p.ty0 q + p.hd
    · exact onType Y p g a0 u0 hu0 q h (hc0 q)
    · exact orth hAdj Y p a0 u0 hu0 heig hV1 q h
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hl2 : 2 ≤ V.l := V.l_prime.two_le
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx _
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have cvA : ActCv Y (fun n => ε ^ V.l ^ n) := fun N i μ => by
    obtain ⟨n0, h⟩ := lSmall_holds C V O dd Y (fun n => ε ^ V.l ^ (n + 1)) (fun n => ε ^ V.l ^ n)
      (pow_cong hl2 hε) N i μ
    exact ⟨n0, h⟩
  have cvB : ActCv Y (fun n => star ε ^ V.l ^ n) := fun N i μ => by
    obtain ⟨n0, h⟩ := lSmall_holds C V O dd Y (fun n => star ε ^ V.l ^ (n + 1)) (fun n => star ε ^ V.l ^ n)
      (pow_cong hl2 hεs) N i μ
    exact ⟨n0, h⟩
  have sA : (fun n => star (ε ^ V.l ^ n)) = fun n => star ε ^ V.l ^ n := funext fun n => star_pow _ _
  obtain ⟨e, eb, he, heb, hib, hadj⟩ := adj_seq hAdj Y (fun n => ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  simp only [star_pow] at heb
  have e1 : linAct e u0 = (1 : C) • u0 :=
    linAct_of_lim Y he (χ := fun n => p.em a0 ε ^ V.l ^ n) (fun n => by rw [heig, map_pow]) (tends_pow_one (hε1 a0))
  rw [one_smul] at e1
  obtain ⟨b, hb⟩ := hPL C V O dd Y d I0 p (star ε) hεs hεs1 hεsx eb heb v
  obtain ⟨wd, hwd, hsat⟩ := p.e_sat
  have hbint : ∀ c, V.Ge 0 (b c) := by
    intro c
    have e : b c = ∑ x, linAct eb v x * wd x c := by
      rw [hb]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ c', ∑ x, b c' * p.e c' x * wd x c = b c' * (if c' = c then 1 else 0) := by
        intro c'
        rw [← hsat c' c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e]
    exact VF.Ge.sum fun x _ => (linAct_int hib hv x).mul_int (hwd x c)
  have h := hadj u0 hu0 hV1 v hv
  rw [e1, hb, aLin_sum_right] at h
  have e2 : Y.aLin u0 v = (Y.aLin u0 v - ∑ c, b c * Y.aLin u0 (p.e c)) + ∑ c, b c * Y.aLin u0 (p.e c) := by ring
  rw [e2]
  exact mm_add h (mm_sum _ _ fun c _ => mm_mul_ge' (hbint c) (hq c))

end Formalism.L2.FormalSeriesBounds
