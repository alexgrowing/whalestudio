import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

private theorem jetSubstP_apply_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S)
    (p : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

theorem swJ_X (m : ℕ) (p : Fin 2 × Fin d) :
    swJ (S := S) d m (Ideal.Quotient.mk _ (X p)) = Ideal.Quotient.mk _ (X (Equiv.swap (0 : Fin 2) 1 p.1, p.2)) := by
  obtain ⟨i, j⟩ := p
  rw [jetSubstP_apply_mk, aeval_X]
  fin_cases i <;> simp

theorem swJ_swJ (m : ℕ) : (swJ (S := S) d m).comp (swJ d m) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, swJ_X, AlgHom.id_apply,
    Equiv.swap_apply_self]

private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]

private theorem degree_add_lemma_3 {τ : Type} (a b : τ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add Finsupp.degree a b
  | (rw [degree_eq_sum_lemma_2, degree_eq_sum_lemma_2, degree_eq_sum_lemma_2]
     exact Finsupp.sum_add_index' (h := fun _ k => k) (fun _ => rfl) (fun _ _ _ => rfl))

private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)

private theorem coeff_eq_zero_of_mem_orig_pow_lemma_5 {τ : Type} (n : ℕ) (x : MvPolynomial τ S)
    (hx : x ∈ orig S τ ^ n) (e : τ →₀ ℕ) (he : e.degree < n) : coeff e x = 0 := by
  classical
  induction n generalizing x e with
  | zero => exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ] at hx
    revert e
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · intro e he
      have hle : orig S τ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial τ S →+* S) :=
        Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp)
      have hb0 : coeff 0 b = 0 := by
        have h0 : MvPolynomial.constantCoeff b = 0 := RingHom.mem_ker.1 (hle hb)
        exact h0
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu' := Finset.HasAntidiagonal.mem_antidiagonal.1 hu
      by_cases h1 : u.1.degree < n
      · rw [ih a ha u.1 h1, zero_mul]
      · have hd : u.1.degree + u.2.degree = e.degree := by rw [← hu', degree_add_lemma_3]
        have h2 : u.2 = 0 := by
          ext i
          have := le_degree_lemma_4 u.2 i
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        rw [h2, hb0, mul_zero]
    · intro e he
      rw [coeff_add, hy e he, hz e he, add_zero]

private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h

private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    coeff e (psTrunc m f) = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]

private theorem mem_orig_pow_of_coeff_lemma_8 {τ : Type} (n : ℕ) (p : MvPolynomial τ S)
    (h : ∀ e : τ →₀ ℕ, e.degree < n → coeff e p = 0) : p ∈ orig S τ ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun e he => ?_
  have hn : n ≤ e.degree := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.1 he) (h e (not_le.1 hlt))
  refine Ideal.pow_le_pow_right hn ?_
  rw [MvPolynomial.monomial_eq, degree_eq_sum_lemma_2, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.mul_mem_left _ _ (Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow ?_ _)
  exact Ideal.subset_span ⟨i, rfl⟩

private theorem psJet_eq_mk_lemma_9 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (p : MvPolynomial τ S)
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ m → coeff e p = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  rw [psJet, Ideal.Quotient.eq]
  refine mem_orig_pow_of_coeff_lemma_8 (m + 1) _ fun e he => ?_
  have he' : e.degree ≤ m := Nat.lt_succ_iff.1 he
  rw [coeff_sub, coeff_psTrunc_lemma_7, if_pos he', h e he', sub_self]

private theorem psJet_mul_lemma_10 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f g : MvPowerSeries τ S) : psJet m (f * g) = psJet m f * psJet m g := by
  show psJet m (f * g) = Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m f) *
    Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m g)
  rw [← map_mul]
  refine psJet_eq_mk_lemma_9 m _ _ fun e he => ?_
  rw [coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hd : x.1.degree + x.2.degree = e.degree := by rw [← hx', degree_add_lemma_3]
  rw [coeff_psTrunc_lemma_7, coeff_psTrunc_lemma_7, if_pos (by omega), if_pos (by omega)]

private theorem psJet_one_lemma_11 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psJet m (1 : MvPowerSeries τ S) = 1 := by
  rw [show (1 : Jet S τ m) = Ideal.Quotient.mk (orig S τ ^ (m + 1)) 1 from (map_one _).symm]
  refine psJet_eq_mk_lemma_9 m 1 1 fun e _ => ?_
  rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]
  by_cases h : e = 0
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem eq_of_psJet_lemma_12 {τ : Type} [Fintype τ] [DecidableEq τ] (f g : MvPowerSeries τ S)
    (h : ∀ m, psJet m f = psJet m g) : f = g := by
  ext e
  have h1 := h e.degree
  rw [psJet, psJet, Ideal.Quotient.eq] at h1
  have h2 := coeff_eq_zero_of_mem_orig_pow_lemma_5 _ _ h1 e (Nat.lt_succ_self _)
  rw [coeff_sub, coeff_psTrunc_lemma_7, coeff_psTrunc_lemma_7, if_pos le_rfl, if_pos le_rfl, sub_eq_zero] at h2
  exact h2

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  have hdeg : (Finsupp.single q 1).degree = 1 := by
    rw [degree_eq_sum_lemma_2, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hs : psTrunc m (MvPowerSeries.X q : MvPowerSeries τ S) = if 1 ≤ m then X q else 0 := by
    ext e
    rw [coeff_psTrunc_lemma_7, MvPowerSeries.coeff_X]
    by_cases h2 : e = Finsupp.single q 1
    · subst h2
      rw [hdeg]
      by_cases h3 : 1 ≤ m
      · simp [h3, MvPolynomial.coeff_X]
      · simp [h3]
    · have h4 : coeff e (X q : MvPolynomial τ S) = 0 := by
        rw [MvPolynomial.coeff_X']
        exact if_neg (Ne.symm h2)
      split_ifs <;> simp [h4, h2]
  rw [Ideal.Quotient.eq, hs]
  split_ifs with h
  · rw [sub_self]
    exact Ideal.zero_mem _
  · have hm : m = 0 := by omega
    subst hm
    rw [zero_sub, zero_add, pow_one]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.subset_span ⟨q, rfl⟩)

private theorem jetMap_mk_lemma_13 {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (p : MvPolynomial κ S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := by
  rfl

theorem psJet_ev_swap (m : ℕ) (f : PS S 2 d) :
    psJet m (ev (n := 2) ![pt S d 1, pt S d 0] f) = swJ d m (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [swJ_X, jetMap_mk_lemma_13, aeval_X]
  fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X]

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [jetSubstP_apply_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem axJ_swJ (m : ℕ) (b : Bool) : (axJ (S := S) d m b).comp (swJ d m) = axJ d m (!b) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, swJ_X, axJ_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, jetMap_mk_lemma_13, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, Units.val_mul, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

theorem unit_eq_one_of_corr (hL : t.PP.L.IsLB) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb t.PP.L φ ε)} (hg : g.IsGen) {v : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ ε g (scaleGenG t φ ε v g)) : v = 1 := by
  have h1 := FBIdLB.scale_eq_of_corr t hL (DVR.corr_refl _ hg) (v := 1) (v' := v)
    (by rw [FBIdLB.scaleGenG_one]; exact h)
  exact h1.symm

theorem sy_unit (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    psJet m sy * swJ d m (psJet m sy) = 1 := by
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hge := hfr.gen m
  have hhh : (homAt x0 (swJ (S := S) d m)).left ≫ (homAt x0 (swJ d m)).left = 𝟙 _ := by
    rw [← Over.comp_left, homAt_comp, swJ_swJ, homAt_id]
    rfl
  have h1 := DVR.corr_pullGen hc (homAt x0 (swJ (S := S) d m)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (swJ (S := S) d m)).left)
    (DVR.corr_trans hL (DVR.corr_pullGen_of_eq (e m) hge _ _ hhh) (DVR.corr_pullGen_id (e m)))
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have h4 := DVR.corr_trans hL hc (FBIdLB.corr_scaleGenG t h3 (unitΓ u⁻¹))
  erw [scaleGenG_scaleGenG] at h4
  have h5 := unit_eq_one_of_corr t hL hge h4
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_mul, ← unitΓ_one] at h5
  have h6 := FBIdLB.unitΓ_injective h5
  have h7 : (u : Jet S (Fin 2 × Fin d) m) * swJ d m u = 1 := by
    have h8 := congrArg (fun w : (Jet S (Fin 2 × Fin d) m)ˣ => (w⁻¹ : (Jet S (Fin 2 × Fin d) m)ˣ)) h6
    simp only [inv_one, mul_inv_rev, inv_inv, map_inv] at h8
    have h9 := congrArg Units.val h8
    simp only [Units.val_one, Units.val_mul, Units.coe_map] at h9
    rw [mul_comm]
    exact h9
  rw [← hu]
  exact h7

theorem sy_inv_of (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) :
    sy * ev (n := 2) ![pt S d 1, pt S d 0] sy = 1 := by
  refine eq_of_psJet_lemma_12 _ _ fun m => ?_
  rw [psJet_mul_lemma_10, psJet_ev_swap, sy_unit t x0 d x hL hfr m, psJet_one_lemma_11]

theorem sy_ax_of (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e)
    (hax : FrAxes t x0 d x e) (b : Bool) :
    ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) sy = 1 := by
  refine psJet_inj fun m => ?_
  rw [psJet_ev_ax, psJet_one]
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hA : ∀ b' : Bool, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b')).left) (LB.oneGen t.PP.L) := by
    intro b'
    cases b'
    · exact (hax m).2
    · exact (hax m).1
  have hcomp : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (swJ (S := S) d m)).left =
      (homAt x0 (axJ (S := S) d m (!b))).left := by
    rw [← Over.comp_left, homAt_comp, axJ_swJ]
  have h1 := DVR.corr_pullGen hc (homAt x0 (axJ (S := S) d m b)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (axJ (S := S) d m b)).left) (DVR.corr_pullGen_of_eq (e m) (hfr.gen m) _ _ hcomp)
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have hAB := DVR.corr_trans hL (hA b) (DVR.corr_symm (hA (!b)))
  have h4 := FBIdLB.scale_eq_of_corr t hL hAB (v := 1)
    (by rw [FBIdLB.scaleGenG_one]; exact h3)
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_one] at h4
  have h5 := FBIdLB.unitΓ_injective h4
  have h6 := congrArg (fun w : (Jet S (Fin 1 × Fin d) m)ˣ => ((w⁻¹ : (Jet S (Fin 1 × Fin d) m)ˣ) :
    Jet S (Fin 1 × Fin d) m)) h5
  simp only [inv_one, Units.val_one, map_inv, inv_inv, Units.coe_map] at h6
  rw [← hu]
  exact h6.symm

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
