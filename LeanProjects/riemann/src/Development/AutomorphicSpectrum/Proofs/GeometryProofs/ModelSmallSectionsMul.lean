import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug

attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.SmallProd

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Small

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hf m1 hm1 k, hg m2 hm2 k]

theorem homog_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem homog_X [DecidableEq K] (k₀ : K) (i₀ : ι k₀) :
    IsMultiHomog (MvPolynomial.X ⟨k₀, i₀⟩ : MRing ι) (Pi.single k₀ 1) := by
  classical
  intro m hm k
  have hm' : m = Finsupp.single ⟨k₀, i₀⟩ 1 := by
    rw [MvPolynomial.X, MvPolynomial.support_monomial, if_neg one_ne_zero] at hm
    exact Finset.mem_singleton.mp hm
  subst hm'
  simp only [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  by_cases hk : k = k₀
  · subst hk
    simp
  · simp [Ne.symm hk, hk]

def mon (c : ∀ k, ι k) (m : K → ℕ) : MRing ι := ∏ k, MvPolynomial.X ⟨k, c k⟩ ^ m k

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (e : ℕ) :
    IsMultiHomog (f ^ e) (e • a) := by
  induction e with
  | zero =>
    have h0 : ((0 : ℕ) • a : K → ℕ) = 0 := by
      ext k
      simp
    rw [pow_zero, h0]
    exact homog_one
  | succ n ih =>
    have h1 : ((n + 1) • a : K → ℕ) = n • a + a := by
      ext k
      simp [add_mul]
    rw [pow_succ, h1]
    exact homog_mul ih hf

theorem homog_mon (c : ∀ k, ι k) (m : K → ℕ) : IsMultiHomog (mon c m) m := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (MvPolynomial.X ⟨k, c k⟩ : MRing ι) ^ m k)
      (∑ k ∈ s, m k • Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty]
      exact homog_one
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact homog_mul (homog_pow (homog_X j (c j)) (m j)) ih
  have hsum : (∑ k, m k • Pi.single k 1 : K → ℕ) = m := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h := key Finset.univ
  rw [hsum] at h
  exact h

private theorem mConeMap_monomial' (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    mConeMap y (MvPolynomial.monomial m r) =
      MvPolynomial.C (aeval y (MvPolynomial.monomial m r : MRing ι)) *
        ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ (∑ i, m ⟨k, i⟩) := by
  classical
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ (∑ i, m ⟨k, i⟩) := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [← hX, mConeMap, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype,
    Finsupp.prod_fintype]
  · simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
    ring
  all_goals simp

theorem cone_form (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  have key : ∀ m ∈ MvPolynomial.support h, mConeMap y (MvPolynomial.monomial m (MvPolynomial.coeff m h)) =
      MvPolynomial.C (aeval y (MvPolynomial.monomial m (MvPolynomial.coeff m h) : MRing ι)) *
        ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    intro m hm
    rw [mConeMap_monomial']
    simp only [hh m hm]
  conv_lhs => rw [MvPolynomial.as_sum h]
  conv_rhs => rw [MvPolynomial.as_sum h]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl key

theorem sub_mem_coord (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hg : IsMultiHomog g d) (e : aeval y f = aeval y g) : f - g ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, cone_form y hf, cone_form y hg, e, sub_self]

theorem aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hm : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, cone_form y hf] at hm
  have hM : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  exact MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hM)

theorem aeval_eq_eval (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    aeval z f = MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem val_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {w w' : ℂ} (h1 : HasVal y a s z w) (h2 : HasVal y a s z w') :
    w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzg⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzg'⟩ := h2
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have e1 := hd k
    have e2 := hd' k
    simp only [Pi.add_apply]
    omega
  have hmem : g * h' - g' * h ∈ mCoordIdeal y := by
    refine sub_mem_coord y (homog_mul hg hh') ?_ ?_
    · rw [hdeg]
      exact homog_mul hg' hh
    · rw [map_mul, map_mul, hy, hy']
      ring
  have h0 := hz.2 _ hmem
  rw [← aeval_eq_eval, map_sub, map_mul, map_mul, hzg, hzg'] at h0
  have hne : aeval z h * aeval z h' ≠ 0 := mul_ne_zero hz0 hz0'
  apply mul_right_cancel₀ hne
  linear_combination h0

theorem val_mul {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (h1 : HasVal y a s z v) (h2 : HasVal y b t z w) : HasVal y (a + b) (s * t) z (v * w) := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzg⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzg'⟩ := h2
  refine ⟨dg + dg', dh + dh', g * g', h * h', homog_mul hg hg', homog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [hd k, hd' k]
  · rw [map_mul, map_mul, hy, hy']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · rw [map_mul, map_mul, hzg, hzg']
    ring

theorem exists_rep (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y)) (a : K → ℤ)
    (s : Ω) : ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y g = s * aeval y h ∧ aeval y h ≠ 0 := by
  classical
  have hc : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hc
  have hmon : ∀ m : K → ℕ, aeval y (mon c m) ≠ 0 := by
    intro m
    simp only [mon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hc k))
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ :=
    hb (s * aeval y (mon c (fun k => (-a k).toNat)) / aeval y (mon c (fun k => (a k).toNat)))
  refine ⟨d + fun k => (a k).toNat, d + fun k => (-a k).toNat, g * mon c (fun k => (a k).toNat),
    h * mon c (fun k => (-a k).toNat), homog_mul hg (homog_mon c _), homog_mul hh (homog_mon c _), ?_, ?_, ?_⟩
  · intro k
    have e1 := Int.toNat_sub_toNat_neg (a k)
    simp only [Pi.add_apply, Nat.cast_add]
    linarith
  · have h1 := hmon (fun k => (a k).toNat)
    rw [map_mul, map_mul, hgh, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff h1]
    ring
  · rw [map_mul]
    exact mul_ne_zero hh0 (hmon _)

theorem lat_mul {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLatNm y a 1)
    (ht : t ∈ chartLatNm y b 1) : s * t ∈ chartLatNm y (a + b) 1 := by
  intro c hc
  have key := mul_mem (hs c hc) (ht c hc)
  convert key using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply]
  ring

theorem valLe_mul (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y))
    (hp : (mCoordIdeal y).IsPrime) (a b : K → ℤ) (s t : Ω) {A B : ((Σ k, ι k) → ℂ) → ℝ} {w w' : MRing ι}
    (hw : IsFormOff (mCoordIdeal y) w) (hw' : IsFormOff (mCoordIdeal y) w')
    (hA : ∀ z ∈ mcPts (mCoordIdeal y), 0 ≤ A z)
    (hs : ∀ z ∈ mcPts (mCoordIdeal y), aeval z w ≠ 0 → ValLe y a s z (A z))
    (ht : ∀ z ∈ mcPts (mCoordIdeal y), aeval z w' ≠ 0 → ValLe y b t z (B z)) :
    ∃ W : MRing ι, IsFormOff (mCoordIdeal y) W ∧ ∀ z ∈ mcPts (mCoordIdeal y), aeval z W ≠ 0 →
      ValLe y (a + b) (s * t) z (A z * B z) := by
  obtain ⟨dg1, dh1, g1, h1, hg1, hh1, hd1, hy1, hy1'⟩ := exists_rep y hb hr a s
  obtain ⟨dg2, dh2, g2, h2, hg2, hh2, hd2, hy2, hy2'⟩ := exists_rep y hb hr b t
  obtain ⟨⟨dw, hdw⟩, hwP⟩ := hw
  obtain ⟨⟨dw', hdw'⟩, hwP'⟩ := hw'
  have hh1P : h1 ∉ mCoordIdeal y := fun hm => hy1' (aeval_eq_zero y hh1 hm)
  have hh2P : h2 ∉ mCoordIdeal y := fun hm => hy2' (aeval_eq_zero y hh2 hm)
  refine ⟨w * w' * h1 * h2, ⟨⟨dw + dw' + dh1 + dh2, homog_mul (homog_mul (homog_mul hdw hdw') hh1) hh2⟩, ?_⟩, ?_⟩
  · intro hm
    rcases hp.mem_or_mem hm with hm | hm
    · rcases hp.mem_or_mem hm with hm | hm
      · rcases hp.mem_or_mem hm with hm | hm
        · exact hwP hm
        · exact hwP' hm
      · exact hh1P hm
    · exact hh2P hm
  · intro z hz hW v hv
    simp only [map_mul] at hW
    obtain ⟨hW1, hz2⟩ := mul_ne_zero_iff.mp hW
    obtain ⟨hW2, hz1⟩ := mul_ne_zero_iff.mp hW1
    obtain ⟨hzw, hzw'⟩ := mul_ne_zero_iff.mp hW2
    have hv1 : HasVal y a s z (aeval z g1 / aeval z h1) :=
      ⟨dg1, dh1, g1, h1, hg1, hh1, hd1, hy1, hz1, (div_mul_cancel₀ _ hz1).symm⟩
    have hv2 : HasVal y b t z (aeval z g2 / aeval z h2) :=
      ⟨dg2, dh2, g2, h2, hg2, hh2, hd2, hy2, hz2, (div_mul_cancel₀ _ hz2).symm⟩
    have hvv := val_unique hz hv (val_mul hv1 hv2)
    rw [hvv, norm_mul]
    exact mul_le_mul (hs z hz hzw _ hv1) (ht z hz hzw' _ hv2) (norm_nonneg _) (hA z hz)

end Forms

section Root

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem nOf_add (u v : GlobalTheory.AllWt.Weight Dw) (j : Option (RootIx Dw)) : nOf (u + v) j = nOf u j + nOf v j := by
  cases j with
  | none => simp [nOf]
  | some r =>
    simp only [nOf]
    exact neg_add (u r.1 r.2) (v r.1 r.2)

theorem degOf_add (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (u v : GlobalTheory.AllWt.Weight Dw) :
    degOf RM (u + v) = degOf RM u + degOf RM v := by
  unfold degOf Top.combLine
  simp only [nOf_add, add_smul, Finset.sum_add_distrib]

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem modelSmall_mul (Or : RootOrigin Y S RM Fx) (u v : GlobalTheory.AllWt.Weight Dw) {R R' : ℝ} (hR : 0 ≤ R)
    {s s' : RM.Ω} (hs : s ∈ modelSmall Or u R) (hs' : s' ∈ modelSmall Or v R') :
    s * s' ∈ modelSmall Or (u + v) (R * R') := by
  obtain ⟨hs1, w, hw, hsw⟩ := hs
  obtain ⟨hs1', w', hw', hsw'⟩ := hs'
  have hprime : (mCoordIdeal RM.y).IsPrime := RM.arith.2.1.1
  have hrel : IsRelevant (mCoordIdeal RM.y) := RM.arith.2.1.2.2
  have hpos : ∀ r, ∀ z ∈ mcPts (mCoordIdeal RM.y), 0 < (Or.sing r).h z :=
    fun r z hz => (Or.sing r).pos z hz.1
  have hA : ∀ z ∈ mcPts (mCoordIdeal RM.y), 0 ≤ R * ∏ r, (Or.sing r).h z ^ nOf u (some r) :=
    fun z hz => mul_nonneg hR (Finset.prod_nonneg fun r _ => (zpow_pos (hpos r z hz) _).le)
  obtain ⟨W, hW, hWz⟩ :=
    valLe_mul RM.y RM.birational hrel hprime (degOf RM u) (degOf RM v) s s' hw hw' hA hsw hsw'
  refine ⟨?_, W, hW, fun z hz hz0 => ?_⟩
  · rw [degOf_add]
    exact lat_mul hs1 hs1'
  · have e : ∀ r, (Or.sing r).h z ^ nOf (u + v) (some r) =
        (Or.sing r).h z ^ nOf u (some r) * (Or.sing r).h z ^ nOf v (some r) := by
      intro r
      rw [nOf_add, zpow_add₀ (hpos r z hz).ne']
    have key : R * R' * ∏ r, (Or.sing r).h z ^ nOf (u + v) (some r) =
        (R * ∏ r, (Or.sing r).h z ^ nOf u (some r)) * (R' * ∏ r, (Or.sing r).h z ^ nOf v (some r)) := by
      simp only [e, Finset.prod_mul_distrib]
      ring
    rw [key, degOf_add]
    exact hWz z hz hz0

end Root

end GlobalTheory.CompanionTheory.Ar.Plug.SmallProd

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem modelSmall_mul_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u v : GlobalTheory.AllWt.Weight Dw) (R R' : ℝ), 0 ≤ R → 0 ≤ R' → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∀ s' ∈ modelSmall (o.toTowerOrigin.Or B b) v R', s * s' ∈ modelSmall (o.toTowerOrigin.Or B b) (u + v) (R * R') :=
  by
  intro E _ _ _ H Dw l Xo c Y _ T o B b u v R R' hR _ s hs s' hs'
  exact SmallProd.modelSmall_mul _ u v hR hs hs'

end GlobalTheory.CompanionTheory.Ar.Plug
