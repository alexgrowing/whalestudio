import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermPointsNoConstantTermFirstZero
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalModuleActionLawsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiplicationByPFactorsFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormulaStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobeniusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Kill

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.DerivEndo

variable {R : Type} [CommRing R] {d : ℕ}

theorem noConst_three {n : ℕ} {a b c : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) :
    NoConst (![a, b, c] : Fin 3 → Pt R n d) := by
  intro j i
  fin_cases j
  exacts [ha i, hb i, hc i]

theorem cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt R n d) i) = 0 := by simp

theorem cc_ptPow {n p : ℕ} (hp : p ≠ 0) (j : Fin n) (i : Fin d) :
    constantCoeff (ptPow R d p j i : PS R n d) = 0 := by
  simp [ptPow, hp]

theorem cc_comp1 {n : ℕ} {V : Pt R 1 d} {a : Pt R n d} (hV : ∀ i, constantCoeff (V i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 V a i) = 0 :=
  (GlobalTheory.DerivEndo.cc_ev (noConst_one ha) _).trans (hV i)

theorem cc_addOf {n : ℕ} {F : Fin d → PS R 2 d} {a b : Pt R n d} (hF : ∀ i, constantCoeff (F i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 :=
  (GlobalTheory.DerivEndo.cc_ev (noConst_two ha hb) _).trans (hF i)

theorem ev_pow' {l m : ℕ} {a : Fin l → Pt R m d} (ha : NoConst a) (f : PS R l d) (n : ℕ) :
    ev a (f ^ n) = ev a f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.DerivEndo.ev_mul ha, ih]

theorem ev_ptPow {l m p : ℕ} {a : Fin l → Pt R m d} (ha : NoConst a) (j : Fin l) (i : Fin d) :
    ev a (ptPow R d p j i) = a j i ^ p := by
  change ev a ((pt R d j i) ^ p) = _
  rw [ev_pow' ha, ev_pt ha]

theorem ev_ptPow_all {n p : ℕ} (hp : p ≠ 0) (f : PS R n d) :
    ev (fun j => ptPow R d p j) f = expand p hp f := by
  simp only [expand, substAlgHom_apply]
  rfl

theorem expand_injective' {n p : ℕ} (hp : p ≠ 0) :
    Function.Injective (expand p hp : PS R n d → PS R n d) := by
  intro f g h
  ext m
  rw [← coeff_expand_smul p hp f m, h, coeff_expand_smul]

theorem inj2 {p : ℕ} (hp : p ≠ 0) {f g : PS R 2 d}
    (h : ev (n := 2) ![ptPow R d p 0, pt R d 1] f = ev (n := 2) ![ptPow R d p 0, pt R d 1] g) : f = g := by
  have n1 : NoConst (![ptPow R d p 0, pt R d 1] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_ptPow hp 0) (cc_pt 1)
  have n2 : NoConst (![pt R d 0, ptPow R d p 1] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_pt 0) (cc_ptPow hp 1)
  have key : ∀ k : PS R 2 d, ev (n := 2) ![pt R d 0, ptPow R d p 1] (ev (n := 2) ![ptPow R d p 0, pt R d 1] k) =
      expand p hp k := by
    intro k
    rw [GlobalTheory.DerivEndo.ev_ev n2 n1, ← ev_ptPow_all hp]
    congr 1
    funext j i
    fin_cases j
    · exact ev_ptPow n2 0 i
    · exact ev_pt n2 1 i
  exact expand_injective' hp (by rw [← key, ← key, h])

theorem inj3 {p : ℕ} (hp : p ≠ 0) {f g : PS R 3 d}
    (h : ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] f = ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] g) :
    f = g := by
  have n1 : NoConst (![ptPow R d p 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_ptPow hp 0) (cc_pt 1) (cc_pt 2)
  have n2 : NoConst (![pt R d 0, ptPow R d p 1, ptPow R d p 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_pt 0) (cc_ptPow hp 1) (cc_ptPow hp 2)
  have key : ∀ k : PS R 3 d, ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2]
      (ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] k) = expand p hp k := by
    intro k
    rw [GlobalTheory.DerivEndo.ev_ev n2 n1, ← ev_ptPow_all hp]
    congr 1
    funext j i
    fin_cases j
    · exact ev_ptPow n2 0 i
    · exact ev_pt n2 1 i
    · exact ev_pt n2 2 i
  exact expand_injective' hp (by rw [← key, ← key, h])

theorem no_constant_evaluation_triple : NoConst (![0, pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) :=
  noConst_three cc_zero (cc_pt 0) (cc_pt 1)

theorem noConst_0x : NoConst (![0, pt R d 0] : Fin 2 → Pt R 1 d) :=
  noConst_two cc_zero (cc_pt 0)

theorem pd_pt_ne {n : ℕ} {j j' : Fin n} {i i' : Fin d} (h : (j', i') ≠ (j, i)) :
    pderiv R (j, i) (pt R d j' i' : PS R n d) = 0 :=
  pderiv_X_of_ne h

theorem pd_ptPow_ne {n p : ℕ} {j j' : Fin n} {i i' : Fin d} (h : (j', i') ≠ (j, i)) :
    pderiv R (j, i) (ptPow R d p j' i' : PS R n d) = 0 := by
  change pderiv R (j, i) ((pt R d j' i') ^ p) = 0
  rw [Derivation.leibniz_pow, pd_pt_ne h, smul_zero, smul_zero]

theorem pd_ptPow_char {n p : ℕ} [CharP R p] (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv R v (ptPow R d p j i : PS R n d) = 0 := by
  change pderiv R v ((pt R d j i) ^ p) = 0
  have h : (p : PS R n d) = 0 := by
    rw [← map_natCast (C (σ := Fin n × Fin d) (R := R)), CharP.cast_eq_zero, map_zero]
  rw [Derivation.leibniz_pow, nsmul_eq_mul, h, zero_mul]

theorem cc_pd {n : ℕ} (v : Fin n × Fin d) (f : PS R n d) :
    constantCoeff (pderiv R v f) = coeff (Finsupp.single v 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem d_zero_pt (h : PS R 2 d) (j : Fin d) :
    pderiv R ((0 : Fin 1), j) (ev (n := 1) ![0, pt R d 0] h) =
      ev (n := 1) ![0, pt R d 0] (pderiv R ((1 : Fin 2), j) h) := by
  have e : ∀ x : Fin d, pderiv R ((0 : Fin 1), j) (X ((0 : Fin 1), x) : PS R 1 d) = if x = j then 1 else 0 := by
    intro x
    by_cases hx : x = j
    · subst hx
      simp
    · rw [if_neg hx]
      exact pderiv_X_of_ne (by simpa using hx)
  rw [pderiv_ev noConst_0x, Fin.sum_univ_two]
  simp [pt, e]

theorem linc (u : Fin d → R) (g : PS R 2 d) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1)
        (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) g)) =
      (bil g 1 1).transpose.mulVec u j := by
  have key : ∀ k : PS R 2 d, coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev (n := 1) ![0, pt R d 0] k) =
      coeff (Finsupp.single ((1 : Fin 2), j) 1) k := by
    intro k
    rw [← cc_pd, d_zero_pt, GlobalTheory.DerivEndo.cc_ev noConst_0x, cc_pd]
  rw [map_sum]
  simp only [coeff_C_mul, key, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_pderiv, bil, add_comm]
  simp [mul_comm]

theorem dz {p : ℕ} [CharP R p] (G : FGLaw R d) (f : PS R 1 d) (c : PS R 2 d) (hp : p ≠ 0)
    (hadd : ev (n := 2) ![pt R d 0] f + ev (n := 2) ![pt R d 1] f =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] c + ev (n := 2) ![addOf G.F (pt R d 0) (pt R d 1)] f)
    (j : Fin d) :
    ∑ k, pderiv R ((0 : Fin 1), k) f * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) (G.F k)) =
      C (coeff (Finsupp.single ((0 : Fin 1), j) 1) f) := by
  have nc : NoConst (![ptPow R d p 0, ptPow R d p 1] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_ptPow hp 0) (cc_ptPow hp 1)
  have hc : pderiv R ((1 : Fin 2), j) (ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] c) = 0 := by
    rw [pderiv_ev nc]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun i _ => ?_
    have : pderiv R ((1 : Fin 2), j) ((![ptPow R d p 0, ptPow R d p 1] : Fin 2 → Pt R 2 d) a i) = 0 := by
      fin_cases a
      · exact pd_ptPow_char _ _ _
      · exact pd_ptPow_char _ _ _
    rw [this, mul_zero]
  have hF : addOf G.F (pt R (n := 2) d 0) (pt R d 1) = G.F := add_pt G
  have h := congrArg (fun g => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) g)) hadd
  rw [hF] at h
  simp only [map_add, GlobalTheory.DerivEndo.ev_add germPointsNoConstantTerm_first_zero, pderiv_second_of_ev_first_point, dy_y, hc, germ_ev_restrict_axis_second_point, GlobalTheory.DerivEndo.ev_zero germPointsNoConstantTerm_first_zero,
    zero_add, pderiv_ev (noConst_one G.const), Fin.sum_univ_one, Matrix.cons_val_zero,
    GlobalTheory.DerivEndo.ev_sum germPointsNoConstantTerm_first_zero, GlobalTheory.DerivEndo.ev_mul germPointsNoConstantTerm_first_zero, germ_ev_restrict_axis_groupLaw, cc_pd] at h
  exact h.symm

theorem inv (G : FGLaw R d) (w : Fin d → PS R 1 d)
    (h : ∀ j, ∑ k, w k * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) (G.F k)) = 0) (k : Fin d) :
    w k = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) (PS R 1 d) :=
    fun k j => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) (G.F k))
  have hA : A.map constantCoeff = 1 := by
    ext k j
    change constantCoeff (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) (G.F k))) = _
    rw [GlobalTheory.DerivEndo.cc_ev germPointsNoConstantTerm_first_zero, ← GlobalTheory.DerivEndo.cc_ev noConst_0x, ← d_zero_pt, G.unit k]
    by_cases hk : k = j
    · subst hk
      simp
    · rw [pderiv_X_of_ne (by simpa using hk), Matrix.one_apply_ne hk, map_zero]
  have hdet : IsUnit A.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff (σ := Fin 1 × Fin d) (R := R)).mapMatrix A = 1 := hA
    rw [this, Matrix.det_one]
    exact isUnit_one
  have hv : Matrix.vecMul w A = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct, A] using h j
  have hw : w = 0 := by
    have := congrArg (fun v => Matrix.vecMul v A⁻¹) hv
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet] using this
  exact congrFun hw k

theorem pd_pt_eq {n : ℕ} (j : Fin n) (i x : Fin d) :
    pderiv R (j, i) (X (j, x) : PS R n d) = if x = i then 1 else 0 := by
  by_cases hx : x = i
  · subst hx
    simp
  · rw [if_neg hx]
    exact pderiv_X_of_ne (by simpa using hx)

theorem partial_derivative_first_evaluation (h : PS R 2 d) (b : Pt R 3 d) (hb0 : ∀ l, constantCoeff (b l) = 0)
    (hb : ∀ i l, pderiv R ((0 : Fin 3), i) (b l) = 0) (i : Fin d) :
    pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0, b] h) =
      ev (n := 3) ![pt R d 0, b] (pderiv R ((0 : Fin 2), i) h) := by
  rw [pderiv_ev (noConst_two (cc_pt 0) hb0), Fin.sum_univ_two]
  simp [pt, pd_pt_eq, hb]

theorem evaluation_zero_first_variable (h : PS R 2 d) (b : Pt R 3 d) (hb0 : ∀ l, constantCoeff (b l) = 0) :
    ev (n := 2) ![0, pt R d 0, pt R d 1] (ev (n := 3) ![pt R d 0, b] h) =
      ev (n := 2) ![fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (b l)] (ev (n := 1) ![0, pt R d 0] h) := by
  have nb : NoConst (![fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (b l)] : Fin 1 → Pt R 2 d) :=
    noConst_one fun l => (GlobalTheory.DerivEndo.cc_ev no_constant_evaluation_triple _).trans (hb0 l)
  rw [GlobalTheory.DerivEndo.ev_ev no_constant_evaluation_triple (noConst_two (cc_pt 0) hb0), GlobalTheory.DerivEndo.ev_ev nb noConst_0x]
  congr 1
  funext j i
  fin_cases j
  · exact (ev_pt no_constant_evaluation_triple 0 i).trans (GlobalTheory.DerivEndo.ev_zero nb).symm
  · exact (ev_pt nb 0 i).symm

theorem dxFirst (u : Fin d → R) (h : PS R 2 d) (b : Pt R 3 d) (hb0 : ∀ l, constantCoeff (b l) = 0)
    (hb : ∀ i l, pderiv R ((0 : Fin 3), i) (b l) = 0) :
    ∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1]
        (pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0, b] h)) =
      ev (n := 2) ![fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (b l)]
        (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) h)) := by
  have nb : NoConst (![fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (b l)] : Fin 1 → Pt R 2 d) :=
    noConst_one fun l => (GlobalTheory.DerivEndo.cc_ev no_constant_evaluation_triple _).trans (hb0 l)
  simp only [partial_derivative_first_evaluation _ b hb0 hb, evaluation_zero_first_variable _ b hb0]
  rw [GlobalTheory.DerivEndo.ev_sum nb]
  simp only [GlobalTheory.DerivEndo.ev_mul nb, GlobalTheory.DerivEndo.ev_C]

theorem dxFrob {p : ℕ} (hp : p ≠ 0) (u : Fin d → R) (φ : PS R 3 d) :
    ∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1]
        (pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] φ)) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
        (∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), i) φ)) := by
  have nA : NoConst (![pt R d 0, ptPow R d p 1, ptPow R d p 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_pt 0) (cc_ptPow hp 1) (cc_ptPow hp 2)
  have nS : NoConst (![ptPow R d p 0, ptPow R d p 1] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_ptPow hp 0) (cc_ptPow hp 1)
  have hd : ∀ (i : Fin d) (k : PS R 3 d), pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] k) =
      ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] (pderiv R ((0 : Fin 3), i) k) := by
    intro i k
    have e1 : ∀ l, pderiv R ((0 : Fin 3), i) (ptPow R d p (1 : Fin 3) l : PS R 3 d) = 0 :=
      fun l => pd_ptPow_ne (by simp)
    have e2 : ∀ l, pderiv R ((0 : Fin 3), i) (ptPow R d p (2 : Fin 3) l : PS R 3 d) = 0 :=
      fun l => pd_ptPow_ne (by simp)
    rw [pderiv_ev nA, Fin.sum_univ_three]
    simp [pt, pd_pt_eq, e1, e2]
  have hv : ∀ k : PS R 3 d, ev (n := 2) ![0, pt R d 0, pt R d 1] (ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] k) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] (ev (n := 2) ![0, pt R d 0, pt R d 1] k) := by
    intro k
    rw [GlobalTheory.DerivEndo.ev_ev no_constant_evaluation_triple nA, GlobalTheory.DerivEndo.ev_ev nS no_constant_evaluation_triple]
    congr 1
    funext j i
    fin_cases j
    · exact (ev_pt no_constant_evaluation_triple 0 i).trans (GlobalTheory.DerivEndo.ev_zero nS).symm
    · exact (ev_ptPow no_constant_evaluation_triple 1 i).trans (ev_pt nS 0 i).symm
    · exact (ev_ptPow no_constant_evaluation_triple 2 i).trans (ev_pt nS 1 i).symm
  simp only [hd, hv]
  rw [GlobalTheory.DerivEndo.ev_sum nS]
  simp only [GlobalTheory.DerivEndo.ev_mul nS, GlobalTheory.DerivEndo.ev_C]

theorem evaluation_zero_composition_invariant (V : Pt R 1 d) (hV : ∀ i, constantCoeff (V i) = 0) (k : PS R 3 d) :
    ev (n := 2) ![0, pt R d 0, pt R d 1] (ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] k) =
      ev (n := 2) ![0, pt R d 0, pt R d 1] k := by
  have nA : NoConst (![comp1 V (pt R d 0), pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_comp1 hV (cc_pt 0)) (cc_pt 1) (cc_pt 2)
  rw [GlobalTheory.DerivEndo.ev_ev no_constant_evaluation_triple nA]
  congr 1
  funext j i
  fin_cases j
  · change ev (n := 2) ![0, pt R d 0, pt R d 1] (ev (n := 3) ![pt R d 0] (V i)) = (0 : PS R 2 d)
    rw [GlobalTheory.DerivEndo.ev_ev no_constant_evaluation_triple (noConst_one (cc_pt 0))]
    have e : (fun (j : Fin 1) (i' : Fin d) => ev (n := 2) ![0, pt R d 0, pt R d 1]
        ((![pt R d 0] : Fin 1 → Pt R 3 d) j i')) = fun _ _ => (0 : PS R 2 d) := by
      funext j i'
      fin_cases j
      exact ev_pt no_constant_evaluation_triple 0 i'
    rw [e, ev_const, hV, map_zero]
  · exact ev_pt no_constant_evaluation_triple 1 i
  · exact ev_pt no_constant_evaluation_triple 2 i

theorem evaluation_zero_derivative_linear_term (V : Pt R 1 d) (i l : Fin d) :
    ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), i) (comp1 V (pt R d 0) l)) =
      C (lin V 1 l i) := by
  have n1 : NoConst (![pt R d 0] : Fin 1 → Pt R 3 d) := noConst_one (cc_pt 0)
  have h : pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0] (V l)) =
      ev (n := 3) ![pt R d 0] (pderiv R ((0 : Fin 1), i) (V l)) := by
    rw [pderiv_ev n1, Fin.sum_univ_one]
    simp [pt, pd_pt_eq]
  change ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 0] (V l))) = _
  rw [h, GlobalTheory.DerivEndo.ev_ev no_constant_evaluation_triple n1]
  have e : (fun (j : Fin 1) (i' : Fin d) => ev (n := 2) ![0, pt R d 0, pt R d 1]
      ((![pt R d 0] : Fin 1 → Pt R 3 d) j i')) = fun _ _ => (0 : PS R 2 d) := by
    funext j i'
    fin_cases j
    exact ev_pt no_constant_evaluation_triple 0 i'
  rw [e, ev_const, cc_pd]
  rfl

theorem dxV (u : Fin d → R) (V : Pt R 1 d) (k : PS R 3 d) (hV : ∀ i, constantCoeff (V i) = 0)
    (hu : (lin V 1).mulVec u = 0) :
    ∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1]
        (pderiv R ((0 : Fin 3), i) (ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] k)) = 0 := by
  have nA : NoConst (![comp1 V (pt R d 0), pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_comp1 hV (cc_pt 0)) (cc_pt 1) (cc_pt 2)
  have hd : ∀ i : Fin d, pderiv R ((0 : Fin 3), i) (ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] k) =
      ∑ l, ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] (pderiv R ((0 : Fin 3), l) k) *
        pderiv R ((0 : Fin 3), i) (comp1 V (pt R d 0) l) := by
    intro i
    have e1 : ∀ l, pderiv R ((0 : Fin 3), i) (pt R d (1 : Fin 3) l : PS R 3 d) = 0 :=
      fun l => pd_pt_ne (by simp)
    have e2 : ∀ l, pderiv R ((0 : Fin 3), i) (pt R d (2 : Fin 3) l : PS R 3 d) = 0 :=
      fun l => pd_pt_ne (by simp)
    rw [pderiv_ev nA, Fin.sum_univ_three]
    simp [e1, e2]
  simp only [hd, GlobalTheory.DerivEndo.ev_sum no_constant_evaluation_triple, GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple, evaluation_zero_composition_invariant V hV, evaluation_zero_derivative_linear_term, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl : ∑ i, (C (lin V 1 l i * u i) : PS R 2 d) = 0 := by
    rw [← map_sum]
    have := congrFun hu l
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [this, map_zero]
  calc _ = ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), l) k) *
        ∑ i, (C (lin V 1 l i * u i) : PS R 2 d) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by rw [hl, mul_zero]

variable {O : Type} [CommRing O] [StarRing O]

theorem ev_addOf {l n : ℕ} {s : Fin l → Pt R n d} (ns : NoConst s) {F : Fin d → PS R 2 d}
    {a b : Pt R l d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    ev s (addOf F a b i) = addOf F (fun q => ev s (a q)) (fun q => ev s (b q)) i := by
  change ev s (ev ![a, b] (F i)) = ev ![fun q => ev s (a q), fun q => ev s (b q)] (F i)
  rw [GlobalTheory.DerivEndo.ev_ev ns (noConst_two ha hb)]
  congr 1
  funext j q
  fin_cases j <;> rfl

theorem ev_step (a : Pt R 1 d) (ha : ∀ i, constantCoeff (a i) = 0) (b : Pt R 3 d)
    (hb : ∀ l, constantCoeff (b l) = 0) (k : PS R 3 d) :
    ev (n := 3) ![pt R d 0, b] (ev (n := 2) ![comp1 a (pt R d 0), pt R d 0, pt R d 1] k) =
      ev (n := 3) ![comp1 a (pt R d 0), pt R d 0, b] k := by
  have n1 : NoConst (![pt R d 0, b] : Fin 2 → Pt R 3 d) := noConst_two (cc_pt 0) hb
  have n2 : NoConst (![comp1 a (pt R d 0), pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) :=
    noConst_three (cc_comp1 ha (cc_pt 0)) (cc_pt 0) (cc_pt 1)
  rw [GlobalTheory.DerivEndo.ev_ev n1 n2]
  congr 1
  funext j i
  fin_cases j
  · change ev (n := 3) ![pt R d 0, b] (ev (n := 2) ![pt R d 0] (a i)) = ev (n := 3) ![pt R d 0] (a i)
    rw [GlobalTheory.DerivEndo.ev_ev n1 (noConst_one (cc_pt 0))]
    congr 1
    funext j l
    fin_cases j
    exact ev_pt n1 0 l
  · exact ev_pt n1 0 i
  · exact ev_pt n1 1 i

theorem inter2 (B : FB R d O) (m : ℕ) :
    ev (n := 3) ![pt R d 0, pt R d 1] (pow1 B m) * ev (n := 3) ![pt R d 0, pt R d 2] (pow1 B m) *
        ev (n := 3) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1, pt R d 2] B.ph2 =
      B.ph2 ^ m * ev (n := 3) ![pt R d 0, B.G.add (pt R d 1) (pt R d 2)] (pow1 B m) := by
  obtain ⟨h0, hs, -, -⟩ := GlobalTheory.T.formal_module_action_laws R d O B
  have cadd : ∀ i, constantCoeff (B.G.add (pt R (n := 3) d 1) (pt R d 2) i) = 0 :=
    cc_addOf B.G.const (cc_pt 1) (cc_pt 2)
  induction m with
  | zero =>
    have e0 : comp1 (B.A.act ((0 : ℕ) : O)) (pt R (n := 3) d 0) = 0 := by
      funext i
      rw [Nat.cast_zero, h0]
      exact GlobalTheory.DerivEndo.ev_zero (noConst_one (cc_pt 0))
    have n1 : NoConst (![pt R d 1, pt R d 2] : Fin 2 → Pt R 3 d) := noConst_two (cc_pt 1) (cc_pt 2)
    have e1 : ev (n := 3) ![(0 : Pt R 3 d), pt R d 1, pt R d 2] B.ph2 = 1 := by
      have := congrArg (ev (n := 3) ![pt R d 1, pt R d 2]) B.cocycleRight_zero_fst
      rw [GlobalTheory.DerivEndo.ev_ev n1 (noConst_three cc_zero (cc_pt 0) (cc_pt 1)), ev_one] at this
      refine Eq.trans ?_ this
      congr 1
      funext j i
      fin_cases j
      · exact (GlobalTheory.DerivEndo.ev_zero n1).symm
      · exact (ev_pt n1 0 i).symm
      · exact (ev_pt n1 1 i).symm
    rw [e0, e1]
    simp [pow1]
  | succ m ih =>
    set a := B.A.act (m : O) with ha
    set T : Pt R 3 d := comp1 a (pt R d 0) with hT
    have a0 : ∀ i, constantCoeff (a i) = 0 := B.A.const _
    have cT : ∀ i, constantCoeff (T i) = 0 := cc_comp1 a0 (cc_pt 0)
    have ns : NoConst (![T, pt R d 0, pt R d 1, pt R d 2] : Fin 4 → Pt R 3 d) := by
      intro j i
      fin_cases j
      exacts [cT i, cc_pt 0 i, cc_pt 1 i, cc_pt 2 i]
    have E : ∀ (c : Fin 3 → Pt R 4 d) (c' : Fin 3 → Pt R 3 d), NoConst c →
        (∀ j i, ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (c j i) = c' j i) → ∀ k : PS R 3 d,
        ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (ev (n := 4) c k) = ev (n := 3) c' k := by
      intro c c' hc h k
      rw [GlobalTheory.DerivEndo.ev_ev ns hc]
      congr 1
      funext j i
      exact h j i
    have q0 : ∀ i, ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (pt R d (0 : Fin 4) i) = T i := ev_pt ns 0
    have q1 : ∀ i, ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (pt R d (1 : Fin 4) i) = pt R d 0 i := ev_pt ns 1
    have q2 : ∀ i, ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (pt R d (2 : Fin 4) i) = pt R d 1 i := ev_pt ns 2
    have q3 : ∀ i, ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2] (pt R d (3 : Fin 4) i) = pt R d 2 i := ev_pt ns 3
    have t1 := E ![pt R d 0, pt R d 1, pt R d 2] ![T, pt R d 0, pt R d 1]
      (noConst_three (cc_pt _) (cc_pt _) (cc_pt _))
      (by intro j i; fin_cases j; exacts [q0 i, q1 i, q2 i]) B.ph1
    have t2 := E ![pt R d 0, pt R d 1, pt R d 3] ![T, pt R d 0, pt R d 2]
      (noConst_three (cc_pt _) (cc_pt _) (cc_pt _))
      (by intro j i; fin_cases j; exacts [q0 i, q1 i, q3 i]) B.ph1
    have t3 := E ![B.G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3]
      ![B.G.add T (pt R d 0), pt R d 1, pt R d 2]
      (noConst_three (cc_addOf B.G.const (cc_pt _) (cc_pt _)) (cc_pt _) (cc_pt _))
      (by
        intro j i
        fin_cases j
        · refine (ev_addOf ns (cc_pt _) (cc_pt _) i).trans ?_
          simp only [q0, q1]
          rfl
        · exact q2 i
        · exact q3 i) B.ph2
    have t4 := E ![pt R d 0, pt R d 2, pt R d 3] ![T, pt R d 1, pt R d 2]
      (noConst_three (cc_pt _) (cc_pt _) (cc_pt _))
      (by intro j i; fin_cases j; exacts [q0 i, q2 i, q3 i]) B.ph2
    have t5 := E ![pt R d 1, pt R d 2, pt R d 3] ![pt R d 0, pt R d 1, pt R d 2]
      (noConst_three (cc_pt _) (cc_pt _) (cc_pt _))
      (by intro j i; fin_cases j; exacts [q1 i, q2 i, q3 i]) B.ph2
    have t6 := E ![pt R d 0, pt R d 1, B.G.add (pt R d 2) (pt R d 3)]
      ![T, pt R d 0, B.G.add (pt R d 1) (pt R d 2)]
      (noConst_three (cc_pt _) (cc_pt _) (cc_addOf B.G.const (cc_pt _) (cc_pt _)))
      (by
        intro j i
        fin_cases j
        · exact q0 i
        · exact q1 i
        · refine (ev_addOf ns (cc_pt _) (cc_pt _) i).trans ?_
          simp only [q2, q3]
          rfl) B.ph1
    have I := congrArg (ev (n := 3) ![T, pt R d 0, pt R d 1, pt R d 2]) B.interchange
    simp only [GlobalTheory.DerivEndo.ev_mul ns] at I
    have t7 : ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] B.ph2 = B.ph2 :=
      ev_pt_self _ (fun j => by fin_cases j <;> rfl) _
    rw [t1, t2, t3, t4, t5, t6, t7] at I
    have hpow : pow1 B (m + 1) = pow1 B m *
        ev (n := 2) ![comp1 a (pt R d 0), pt R d 0, pt R d 1] B.ph1 := by
      rw [pow1, Finset.prod_range_succ]
      rfl
    have hact : comp1 (B.A.act ((m + 1 : ℕ) : O)) (pt R (n := 3) d 0) = B.G.add T (pt R d 0) := by
      rw [hs m]
      funext i
      change ev (n := 3) ![pt R d 0] (ev (n := 1) ![a, pt R d 0] (B.G.F i)) = ev (n := 3) ![T, pt R d 0] (B.G.F i)
      rw [GlobalTheory.DerivEndo.ev_ev (noConst_one (cc_pt 0)) (noConst_two a0 (cc_pt 0))]
      congr 1
      funext j l
      fin_cases j
      · rfl
      · exact ev_pt (noConst_one (cc_pt 0)) 0 l
    have n1 : NoConst (![pt R d 0, pt R d 1] : Fin 2 → Pt R 3 d) := noConst_two (cc_pt 0) (cc_pt 1)
    have n2 : NoConst (![pt R d 0, pt R d 2] : Fin 2 → Pt R 3 d) := noConst_two (cc_pt 0) (cc_pt 2)
    have n3 : NoConst (![pt R d 0, B.G.add (pt R d 1) (pt R d 2)] : Fin 2 → Pt R 3 d) :=
      noConst_two (cc_pt 0) cadd
    rw [hact, hpow, GlobalTheory.DerivEndo.ev_mul n1, GlobalTheory.DerivEndo.ev_mul n2, GlobalTheory.DerivEndo.ev_mul n3,
      ev_step a a0 _ (cc_pt 1), ev_step a a0 _ (cc_pt 2), ev_step a a0 _ cadd]
    rw [pow_succ]
    linear_combination
      (ev (n := 3) ![pt R d 0, pt R d 1] (pow1 B m) * ev (n := 3) ![pt R d 0, pt R d 2] (pow1 B m)) * I +
      (B.ph2 * ev (n := 3) ![T, pt R d 0, B.G.add (pt R d 1) (pt R d 2)] B.ph1) * ih

theorem identity {p : ℕ} [Fact p.Prime] [CharP R p] (B : FB R d O) (V : Pt R 1 d) (g : PS R 2 d)
    (hV0 : ∀ i, constantCoeff (V i) = 0) (hV : B.A.act (p : O) = comp1 V (ptPow R d p 0))
    (hg : pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g) :
    ev (n := 3) ![pt R d 0, pt R d 1] g * ev (n := 3) ![pt R d 0, pt R d 2] g *
        ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] B.ph2 =
      ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] (MvPowerSeries.map (frobenius R p) B.ph2) *
        ev (n := 3) ![pt R d 0, addOf B.G.F (pt R d 1) (pt R d 2)] g := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have ns : NoConst (![ptPow R d p 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) :=
    noConst_three (cc_ptPow hp 0) (cc_pt 1) (cc_pt 2)
  have s0 : ∀ i, ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (pt R d (0 : Fin 3) i) = ptPow R d p 0 i :=
    ev_pt ns 0
  have s1 : ∀ i, ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (pt R d (1 : Fin 3) i) = pt R d 1 i := ev_pt ns 1
  have s2 : ∀ i, ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (pt R d (2 : Fin 3) i) = pt R d 2 i := ev_pt ns 2
  have np : NoConst (![ptPow R d p 0, pt R d 1] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_ptPow hp 0) (cc_pt 1)
  have A : ∀ b : Pt R 3 d, (∀ l, constantCoeff (b l) = 0) →
      (∀ l, ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (b l) = b l) →
      ev (n := 3) ![pt R d 0, b] (pow1 B p) =
        ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (ev (n := 3) ![pt R d 0, b] g) := by
    intro b hb0 hb
    have n1 : NoConst (![pt R d 0, b] : Fin 2 → Pt R 3 d) := noConst_two (cc_pt 0) hb0
    rw [hg, GlobalTheory.DerivEndo.ev_ev n1 np, GlobalTheory.DerivEndo.ev_ev ns n1]
    congr 1
    funext j i
    fin_cases j
    · exact (ev_ptPow n1 0 i).trans (s0 i).symm
    · exact (ev_pt n1 1 i).trans (hb i).symm
  have cadd : ∀ i, constantCoeff (addOf B.G.F (pt R (n := 3) d 1) (pt R d 2) i) = 0 :=
    cc_addOf B.G.const (cc_pt 1) (cc_pt 2)
  have a3 : ∀ l, ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (addOf B.G.F (pt R d 1) (pt R d 2) l) =
      addOf B.G.F (pt R d 1) (pt R d 2) l := by
    intro l
    refine (ev_addOf ns (cc_pt _) (cc_pt _) l).trans ?_
    simp only [s1, s2]
  have A3 : ev (n := 3) ![comp1 (B.A.act (p : O)) (pt R d 0), pt R d 1, pt R d 2] B.ph2 =
      ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2]
        (ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] B.ph2) := by
    have n1 : NoConst (![comp1 V (pt R d 0), pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) :=
      noConst_three (cc_comp1 hV0 (cc_pt 0)) (cc_pt 1) (cc_pt 2)
    rw [GlobalTheory.DerivEndo.ev_ev ns n1, hV]
    congr 1
    funext j i
    fin_cases j
    · change ev (n := 3) ![pt R d 0] (ev (n := 1) ![ptPow R d p 0] (V i)) =
        ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2] (ev (n := 3) ![pt R d 0] (V i))
      have m1 : NoConst (![pt R d 0] : Fin 1 → Pt R 3 d) := noConst_one (cc_pt 0)
      rw [GlobalTheory.DerivEndo.ev_ev m1 (noConst_one (cc_ptPow hp 0)), GlobalTheory.DerivEndo.ev_ev ns m1]
      congr 1
      funext j l
      fin_cases j
      exact (ev_ptPow m1 0 l).trans (s0 l).symm
    · exact (s1 i).symm
    · exact (s2 i).symm
  have A4 : B.ph2 ^ p = ev (n := 3) ![ptPow R d p 0, pt R d 1, pt R d 2]
      (ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] (MvPowerSeries.map (frobenius R p) B.ph2)) := by
    have n1 : NoConst (![pt R d 0, ptPow R d p 1, ptPow R d p 2] : Fin 3 → Pt R 3 d) :=
      noConst_three (cc_pt 0) (cc_ptPow hp 1) (cc_ptPow hp 2)
    rw [GlobalTheory.T.power_series_pow_p_frobenius R p d 3 B.ph2, GlobalTheory.DerivEndo.ev_ev ns n1]
    congr 1
    funext j i
    fin_cases j
    · exact (s0 i).symm
    · exact (ev_ptPow ns 1 i).symm
    · exact (ev_ptPow ns 2 i).symm
  apply inj3 hp
  have I := inter2 B p
  rw [A _ (cc_pt 1) s1, A _ (cc_pt 2) s2, A3, A4] at I
  have I2 : ev (n := 3) ![pt R d 0, addOf B.G.F (pt R d 1) (pt R d 2)] (pow1 B p) = _ := A _ cadd a3
  change _ = _ * ev (n := 3) ![pt R d 0, addOf B.G.F (pt R d 1) (pt R d 2)] (pow1 B p) at I
  rw [I2] at I
  rw [GlobalTheory.DerivEndo.ev_mul ns, GlobalTheory.DerivEndo.ev_mul ns, GlobalTheory.DerivEndo.ev_mul ns]
  exact I

theorem additive {p : ℕ} (hp : p ≠ 0) (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (u : Fin d → R)
    (g : PS R 2 d) (ph φ : PS R 3 d) (V : Pt R 1 d) (hV : ∀ i, constantCoeff (V i) = 0)
    (hu : (lin V 1).mulVec u = 0) (hg : ev (n := 1) ![0, pt R d 0] g = 1)
    (hph : ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1)
    (hid : ev (n := 3) ![pt R d 0, pt R d 1] g * ev (n := 3) ![pt R d 0, pt R d 2] g *
        ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] ph =
      ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] φ *
        ev (n := 3) ![pt R d 0, addOf F (pt R d 1) (pt R d 2)] g) :
    ev (n := 2) ![pt R d 0] (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) g)) +
        ev (n := 2) ![pt R d 1] (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) g)) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
          (∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), i) φ)) +
        ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)]
          (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) g)) := by
  let Dl : PS R 3 d → PS R 2 d := fun h =>
    ∑ i, C (u i) * ev (n := 2) ![0, pt R d 0, pt R d 1] (pderiv R ((0 : Fin 3), i) h)
  have leib : ∀ a b : PS R 3 d, Dl (a * b) =
      ev (n := 2) ![0, pt R d 0, pt R d 1] a * Dl b + ev (n := 2) ![0, pt R d 0, pt R d 1] b * Dl a := by
    intro a b
    simp only [Dl, Derivation.leibniz, smul_eq_mul, GlobalTheory.DerivEndo.ev_add no_constant_evaluation_triple,
      GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have p1 : ∀ i l, pderiv R ((0 : Fin 3), i) (pt R d (1 : Fin 3) l : PS R 3 d) = 0 :=
    fun i l => pd_pt_ne (by simp)
  have p2 : ∀ i l, pderiv R ((0 : Fin 3), i) (pt R d (2 : Fin 3) l : PS R 3 d) = 0 :=
    fun i l => pd_pt_ne (by simp)
  have cadd : ∀ i, constantCoeff (addOf F (pt R (n := 3) d 1) (pt R d 2) i) = 0 :=
    cc_addOf hF (cc_pt 1) (cc_pt 2)
  have p3 : ∀ i l, pderiv R ((0 : Fin 3), i) (addOf F (pt R (n := 3) d 1) (pt R d 2) l) = 0 := by
    intro i l
    change pderiv R ((0 : Fin 3), i) (ev (n := 3) ![pt R d 1, pt R d 2] (F l)) = 0
    rw [pderiv_ev (noConst_two (cc_pt 1) (cc_pt 2)), Fin.sum_univ_two]
    simp [p1, p2]
  have f1 : (fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (pt R d (1 : Fin 3) l)) = pt R d 0 :=
    funext fun l => ev_pt no_constant_evaluation_triple 1 l
  have f2 : (fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (pt R d (2 : Fin 3) l)) = pt R d 1 :=
    funext fun l => ev_pt no_constant_evaluation_triple 2 l
  have f3 : (fun l => ev (n := 2) ![0, pt R d 0, pt R d 1] (addOf F (pt R (n := 3) d 1) (pt R d 2) l)) =
      addOf F (pt R d 0) (pt R d 1) := by
    funext l
    refine (ev_addOf no_constant_evaluation_triple (cc_pt _) (cc_pt _) l).trans ?_
    rw [f1, f2]
  have d1 := dxFirst u g (pt R d 1) (cc_pt 1) (p1 ·)
  have d2 := dxFirst u g (pt R d 2) (cc_pt 2) (p2 ·)
  have d4 := dxFirst u g (addOf F (pt R d 1) (pt R d 2)) cadd p3
  rw [f1] at d1
  rw [f2] at d2
  rw [f3] at d4
  have d3 := dxV u V ph hV hu
  have dQ := dxFrob (R := R) (d := d) hp u φ
  have v1 := evaluation_zero_first_variable g (pt R d 1) (cc_pt 1)
  have v2 := evaluation_zero_first_variable g (pt R d 2) (cc_pt 2)
  have v4 := evaluation_zero_first_variable g (addOf F (pt R d 1) (pt R d 2)) cadd
  rw [hg, ev_one] at v1 v2 v4
  have v3 := evaluation_zero_composition_invariant V hV ph
  rw [hph] at v3
  have vQ := congrArg (ev (n := 2) ![0, pt R d 0, pt R d 1]) hid
  rw [GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple, GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple, GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple,
    v1, v2, v3, v4, _root_.one_mul, _root_.one_mul, _root_.mul_one] at vQ
  have h := congrArg Dl hid
  rw [leib, leib, leib, GlobalTheory.DerivEndo.ev_mul no_constant_evaluation_triple, v1, v2, v3, v4, ← vQ] at h
  have d1' : Dl (ev (n := 3) ![pt R d 0, pt R d 1] g) = _ := d1
  have d2' : Dl (ev (n := 3) ![pt R d 0, pt R d 2] g) = _ := d2
  have d3' : Dl (ev (n := 3) ![comp1 V (pt R d 0), pt R d 1, pt R d 2] ph) = _ := d3
  have d4' : Dl (ev (n := 3) ![pt R d 0, addOf F (pt R d 1) (pt R d 2)] g) = _ := d4
  have dQ' : Dl (ev (n := 3) ![pt R d 0, ptPow R d p 1, ptPow R d p 2] φ) = _ := dQ
  rw [d1', d2', d3', d4', dQ'] at h
  linear_combination h

theorem germKill : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv R ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv R ((0 : Fin 2), i) g)) = 0 := by
  intro R _ p _ _ d O _ _ B u g hal hg j
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [alpha_apply] at hal
  have h1 : (hw B p).mulVec u = 0 := congrArg Prod.fst hal
  have h2 : (am B p).transpose.mulVec u = 0 := congrArg Prod.snd hal
  obtain ⟨V, hV0, hVact, hVlin⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B
  obtain ⟨g₀, hax, hg₀, hbil⟩ := GlobalTheory.T.pow_one_series_p_formula R p d O B
  obtain rfl : g = g₀ := inj2 hp (hg.symm.trans hg₀)
  have hid := identity B V g hV0 hVact hg
  have hadd := additive hp B.G.F B.G.const u g B.ph2 (MvPowerSeries.map (frobenius R p) B.ph2) V hV0
    (by rw [hVlin]; exact h1) hax.1 B.cocycleRight_zero_fst hid
  have hz := dz B.G _ _ hp hadd
  refine inv B.G (fun k => pderiv R ((0 : Fin 1), k)
    (∑ i, C (u i) * ev (n := 1) ![0, pt R d 0] (pderiv R ((0 : Fin 2), i) g))) (fun j' => ?_) j
  rw [hz j', linc, hbil, h2]
  simp

end GlobalTheory.CompanionTheory.Ar.Kill
