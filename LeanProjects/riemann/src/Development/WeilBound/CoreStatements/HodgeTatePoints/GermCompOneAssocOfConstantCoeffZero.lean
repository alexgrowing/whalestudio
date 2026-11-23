import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP

noncomputable section

namespace PositivityTheory.HtPt.Ca

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

variable {R : Type} [CommRing R] {d : ℕ}

def Z {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def ZZ {m n : ℕ} (a : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

def evP {m n : ℕ} (b : Fin m → Pt R n d) (a : Pt R m d) : Pt R n d := fun i => ev b (a i)

theorem ev_zero {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) : ev a (0 : PS R m d) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_zero' ha

private theorem ev_sub_lemma {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) :
    MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

private theorem ev_sub_lemma_2 {σ : Type} (g : MvPowerSeries σ R) (hg : constantCoeff g = 0) :
    (1 : ℕ∞) ≤ g.order := by
  refine le_order fun e he => ?_
  have h0 : e.degree = 0 := by
    norm_cast at he
    omega
  rw [(Finsupp.degree_eq_zero_iff e).mp h0, coeff_zero_eq_constantCoeff_apply, hg]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (f : PS R m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : constantCoeff (ev a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero (ev_sub_lemma ha) (fun p => ha p.1 p.2) (by simp)
  have e : ev a f = ev a (C (constantCoeff f)) + ev a (f - C (constantCoeff f)) := by
    rw [← ev_add a ha, add_sub_cancel]
  rw [e, map_add, h0, ev_C, constantCoeff_C, add_zero]

theorem ev_ev {l m n : ℕ} {a : Fin l → Pt R m d} {b : Fin m → Pt R n d} (ha : ZZ a) (hb : ZZ b) (f : PS R l d) :
    ev b (ev a f) = ev (fun j => evP b (a j)) f :=
  ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_ev a b ha hb f

theorem Z_zero {n : ℕ} : Z (0 : Pt R n d) := fun _ => by simp

theorem Z_pt {n : ℕ} (j : Fin n) : Z (pt R d j) := fun _ => by simp [pt]

theorem Z_ptPow {n p : ℕ} (hp : 1 ≤ p) (j : Fin n) : Z (ptPow R d p j) := fun _ => by
  simp [ptPow, zero_pow (by omega : p ≠ 0)]

theorem cechDeRhamTotalCocyclesOne {n : ℕ} {a : Pt R n d} (ha : Z a) : ZZ ![a] := by
  intro j i
  fin_cases j
  simpa using ha i

theorem cechDeRhamTotalCocyclesTwo {n : ℕ} {a b : Pt R n d} (ha : Z a) (hb : Z b) : ZZ ![a, b] := by
  intro j i
  fin_cases j
  · simpa using ha i
  · simpa using hb i

theorem zero_constant_triple {n : ℕ} {a b c : Pt R n d} (ha : Z a) (hb : Z b) (hc : Z c) : ZZ ![a, b, c] := by
  intro j i
  fin_cases j
  · simpa using ha i
  · simpa using hb i
  · simpa using hc i

theorem Z_evP {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) {a : Pt R m d} (ha : Z a) : Z (evP b a) := by
  intro i
  exact (cc_ev hb (a i)).trans (ha i)

theorem Z_comp1 {n : ℕ} {φ : Pt R 1 d} (hφ : Z φ) {a : Pt R n d} (ha : Z a) : Z (comp1 φ a) :=
  Z_evP (cechDeRhamTotalCocyclesOne ha) hφ

theorem germ_ev_ev_single_point_comp {m n : ℕ} {a : Pt R m d} {b : Fin m → Pt R n d} (ha : Z a) (hb : ZZ b) (f : PS R 1 d) :
    ev b (ev ![a] f) = ev ![evP b a] f := by
  rw [ev_ev (cechDeRhamTotalCocyclesOne ha) hb]; congr 1; funext j; fin_cases j; rfl

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) : evP b (pt R d j) = b j :=
  funext fun i => ev_X b hb j i

theorem evalPoints_zero {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) : evP b 0 = 0 :=
  funext fun _ => ev_zero hb

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (φ : Pt R 1 d) {a : Pt R m d} (ha : Z a) :
    evP b (comp1 φ a) = comp1 φ (evP b a) :=
  funext fun i => germ_ev_ev_single_point_comp ha hb (φ i)

theorem germCompOne_assoc_of_constantCoeff_zero {n : ℕ} (φ : Pt R 1 d) {ψ : Pt R 1 d} (hψ : Z ψ) {a : Pt R n d} (ha : Z a) :
    comp1 (comp1 φ ψ) a = comp1 φ (comp1 ψ a) :=
  evalPoints_comp (cechDeRhamTotalCocyclesOne ha) φ hψ

theorem germComp1_zero_of_noConstantCoeff {n : ℕ} {φ : Pt R 1 d} (hφ : Z φ) : comp1 φ (0 : Pt R n d) = 0 := by
  funext i
  have hs := ev_sub_lemma (cechDeRhamTotalCocyclesOne (Z_zero (R := R) (n := n) (d := d)))
  have h1 : (1 : ℕ∞) ≤ (φ i).order := ev_sub_lemma_2 _ (hφ i)
  have h2 : (⊤ : ℕ∞) ≤ (ev ![(0 : Pt R n d)] (φ i)).order := by
    refine le_trans ?_ (le_order_subst hs (φ i))
    have ht : (⨅ p : Fin 1 × Fin d, (![(0 : Pt R n d)] p.1 p.2).order) = ⊤ := by
      simp
    rw [ht, ENat.top_mul (by intro h; rw [h] at h1; simp at h1)]
  exact order_eq_top_iff.mp (top_le_iff.mp h2)

theorem coeff_single_one {σ : Type} (s : σ) (f : MvPowerSeries σ R) :
    coeff (Finsupp.single s 1) f = constantCoeff (pderiv R s f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]; simp

theorem coeff_add_single {σ : Type} (D : σ →₀ ℕ) (t : σ) (h : D t = 0) (f : MvPowerSeries σ R) :
    coeff (D + Finsupp.single t 1) f = coeff D (pderiv R t f) := by
  rw [coeff_pderiv, h]; simp

private theorem cc_d_ev_lemma {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (g : PS R m d) :
    ev a g = substAlgHom (ev_sub_lemma ha) g := by
  rw [substAlgHom_apply]
  rfl

private theorem cc_d_ev_lemma_2 {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (t : Fin n × Fin d)
    (P : MvPolynomial (Fin m × Fin d) R) :
    pderiv R t (ev a (P : PS R m d)) =
      ∑ p : Fin m × Fin d, ev a (pderiv R p (P : PS R m d)) * pderiv R t (a p.1 p.2) := by
  classical
  simp only [cc_d_ev_lemma ha]
  induction P using MvPolynomial.induction_on
  next r =>
    rw [MvPolynomial.coe_C, ← cc_d_ev_lemma ha, ev_C, pderiv_C]
    simp [-coe_substAlgHom, -substAlgHom_apply]
  next p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p k hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, substAlgHom_X, Derivation.leibniz,
      smul_eq_mul, hp, map_add, pderiv_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp [apply_ite, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, -coe_substAlgHom,
      -substAlgHom_apply]

private theorem cc_d_ev_lemma_3 {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) {K : ℕ} {g : PS R m d}
    (hg : ∀ e : Fin m × Fin d →₀ ℕ, e.degree < K → coeff e g = 0) :
    ∀ e : Fin n × Fin d →₀ ℕ, e.degree < K → coeff e (ev a g) = 0 := by
  intro e he
  apply coeff_of_lt_order
  have h1 : (1 : ℕ∞) ≤ ⨅ p : Fin m × Fin d, (a p.1 p.2).order :=
    le_iInf fun p => ev_sub_lemma_2 _ (ha p.1 p.2)
  have h2 : (K : ℕ∞) ≤ g.order := le_order fun x hx => hg x (by exact_mod_cast hx)
  calc (e.degree : ℕ∞) < K := by exact_mod_cast he
    _ = 1 * K := (one_mul _).symm
    _ ≤ (⨅ p : Fin m × Fin d, (a p.1 p.2).order) * g.order := mul_le_mul' h1 h2
    _ ≤ (ev a g).order := le_order_subst (ev_sub_lemma ha) g

private theorem cc_d_ev_lemma_4 {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (t : Fin n × Fin d)
    (f : PS R m d) :
    pderiv R t (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv R p f) * pderiv R t (a p.1 p.2) := by
  ext e
  have hh : ∀ x : Fin m × Fin d →₀ ℕ, x.degree < e.degree + 2 →
      coeff x (f - ((truncTotal (e.degree + 2) f : MvPolynomial (Fin m × Fin d) R) : PS R m d)) = 0 := by
    intro x hx
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]
  set P : MvPolynomial (Fin m × Fin d) R := truncTotal (e.degree + 2) f with hP
  have hL : coeff e (pderiv R t (ev a (f - (P : PS R m d)))) = 0 := by
    rw [coeff_pderiv, cc_d_ev_lemma_3 ha hh _ ?_, zero_mul]
    simp [map_add, Finsupp.degree_single]
  have hR : coeff e (∑ p : Fin m × Fin d,
      ev a (pderiv R p (f - (P : PS R m d))) * pderiv R t (a p.1 p.2)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree ≤ e.degree := by
      rw [← hx']
      simp [map_add]
    rw [cc_d_ev_lemma_3 ha (K := e.degree + 1) ?_ x.1 (by omega), zero_mul]
    intro y hy
    rw [coeff_pderiv, hh _ (by simp [map_add, Finsupp.degree_single]; omega), zero_mul]
  have lin1 : pderiv R t (ev a f) = pderiv R t (ev a (P : PS R m d)) + pderiv R t (ev a (f - P)) := by
    rw [← map_add, ← ev_add a ha, add_sub_cancel]
  have lin2 : (∑ p : Fin m × Fin d, ev a (pderiv R p f) * pderiv R t (a p.1 p.2)) =
      (∑ p : Fin m × Fin d, ev a (pderiv R p (P : PS R m d)) * pderiv R t (a p.1 p.2)) +
      ∑ p : Fin m × Fin d, ev a (pderiv R p (f - (P : PS R m d))) * pderiv R t (a p.1 p.2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← add_mul, ← ev_add a ha, ← map_add, add_sub_cancel]
  rw [lin1, lin2, map_add, map_add, hL, hR, cc_d_ev_lemma_2 ha t P]

theorem cc_d_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (t : Fin n × Fin d) (f : PS R m d) :
    constantCoeff (pderiv R t (ev a f)) =
      ∑ p : Fin m × Fin d, constantCoeff (pderiv R p f) * constantCoeff (pderiv R t (a p.1 p.2)) := by
  rw [cc_d_ev_lemma_4 ha t f, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, cc_ev ha]

theorem cc_dd_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ZZ a) (s t : Fin n × Fin d) (f : PS R m d)
    (hf : ∀ p, constantCoeff (pderiv R p f) = 0) :
    constantCoeff (pderiv R s (pderiv R t (ev a f))) =
      ∑ p : Fin m × Fin d, (∑ q : Fin m × Fin d, constantCoeff (pderiv R q (pderiv R p f)) *
        constantCoeff (pderiv R s (a q.1 q.2))) * constantCoeff (pderiv R t (a p.1 p.2)) := by
  rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_ev a ha, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, cc_ev ha, hf, zero_mul, zero_add,
    cc_d_ev ha, mul_comm]

theorem lin_one (φ : Pt R 1 d) (i j : Fin d) : lin φ 1 i j = constantCoeff (pderiv R ((0 : Fin 1), j) (φ i)) :=
  coeff_single_one _ _

theorem cc_d_comp1_pt {n : ℕ} (φ : Pt R 1 d) (j k : Fin n) (i l : Fin d) :
    constantCoeff (pderiv R (k, l) (comp1 φ (pt R d j) i)) = if j = k then lin φ 1 i l else 0 := by
  classical
  show constantCoeff (pderiv R (k, l) (ev ![pt R d j] (φ i))) = _
  rw [cc_d_ev (cechDeRhamTotalCocyclesOne (Z_pt j)), lin_one, Fintype.sum_prod_type, Fin.sum_univ_one]
  by_cases h : j = k
  · subst h
    simp [pt, pderiv_X, Pi.single_apply]
  · simp [pt, pderiv_X, Pi.single_apply, h, Ne.symm h]

theorem lin_comp1 (φ : Pt R 1 d) {ψ : Pt R 1 d} (hψ : Z ψ) : lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 := by
  ext i j
  rw [lin_one, Matrix.mul_apply]
  show constantCoeff (pderiv R ((0 : Fin 1), j) (ev ![ψ] (φ i))) = _
  rw [cc_d_ev (cechDeRhamTotalCocyclesOne hψ), Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [lin_one]

theorem coeff_subst_pow {σ : Type} [Fintype σ] (w : σ → ℕ) (hw : ∀ s, 1 ≤ w s) (f : MvPowerSeries σ R)
    (D E : σ →₀ ℕ) (h : ∀ t, E t = w t * D t) :
    coeff E (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) f) = coeff D f := by
  classical
  have key : ∀ (S : Finset σ) (g : σ → ℕ),
      ∏ s ∈ S, (X s : MvPowerSeries σ R) ^ g s = monomial (∑ s ∈ S, Finsupp.single s (g s)) 1 := by
    intro S g
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, mul_one]
  have hs : HasSubst (fun s => (X s : MvPowerSeries σ R) ^ w s) :=
    hasSubst_of_constantCoeff_zero (fun s => by
      simp [zero_pow (show w s ≠ 0 by have := hw s; omega)])
  have hp : ∀ D' : σ →₀ ℕ, (D'.prod fun s e => ((X s : MvPowerSeries σ R) ^ w s) ^ e) =
      monomial (∑ s ∈ D'.support, Finsupp.single s (w s * D' s)) 1 := by
    intro D'
    rw [Finsupp.prod, ← key]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← pow_mul]
  have hpt : ∀ (D' : σ →₀ ℕ) t, (∑ s ∈ D'.support, Finsupp.single s (w s * D' s)) t = w t * D' t := by
    intro D' t
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with ht
    · rfl
    · rw [Finsupp.notMem_support_iff.mp ht, mul_zero]
  have hev : ∀ D' : σ →₀ ℕ, E = (∑ s ∈ D'.support, Finsupp.single s (w s * D' s)) ↔ D' = D := by
    intro D'
    constructor
    · intro h'
      ext t
      have := hpt D' t
      rw [← h', h t] at this
      exact (Nat.eq_of_mul_eq_mul_left (hw t) this).symm
    · rintro rfl
      ext t
      rw [hpt, h]
  rw [coeff_subst hs, finsum_eq_single _ D]
  · rw [hp, coeff_monomial, if_pos ((hev D).mpr rfl), smul_eq_mul, mul_one]
  · intro D' hD'
    rw [hp, coeff_monomial, if_neg, smul_zero]
    intro h'
    exact hD' ((hev D').mp h')

theorem lin_ptPow (φ : Pt R 1 d) {p : ℕ} (hp : 1 ≤ p) : lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 := by
  ext i j
  have hx : (fun q : Fin 1 × Fin d => (![ptPow R d p 0] : Fin 1 → Pt R 1 d) q.1 q.2) =
      fun q => (X q : MvPowerSeries (Fin 1 × Fin d) R) ^ (fun _ => p) q := by
    funext q
    obtain ⟨q1, q2⟩ := q
    fin_cases q1
    rfl
  show coeff (Finsupp.single ((0 : Fin 1), j) p)
      (subst (fun q : Fin 1 × Fin d => (![ptPow R d p 0] : Fin 1 → Pt R 1 d) q.1 q.2) (φ i)) =
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)
  rw [hx, coeff_subst_pow (fun _ => p) (fun _ => hp) (φ i) (Finsupp.single (0, j) 1) _ ?_]
  intro t
  simp only [Finsupp.single_apply]
  split_ifs <;> simp

theorem lin_comp : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 :=
  fun _ _ _ φ _ _ hψ => ⟨lin_comp1 φ hψ, lin_pt_eq_one, fun _ hp => ⟨lin_ptPow φ hp, by
    rw [← germCompOne_assoc_of_constantCoeff_zero φ hψ (Z_ptPow hp 0), lin_ptPow _ hp, lin_comp1 φ hψ]⟩⟩

end PositivityTheory.HtPt.Ca
