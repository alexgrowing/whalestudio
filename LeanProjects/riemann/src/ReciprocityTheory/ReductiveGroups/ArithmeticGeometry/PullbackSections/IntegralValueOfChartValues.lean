import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueBoundRamified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PlaceBoundOwnPrimeOf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def HarmonicValueAtIntegralPoint : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (T' : CDVR) (io' : T.Q.c.F →+* T'.Fr) (e' : ℕ) (yI' : IntFr (T.Q.Xo j) T.Q.c T' io'),
        OverLa la T'.V io' e' ∧ yI'.IsAlg ∧
        ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io' yI') (P' : MvPolynomial (LtN (T.Q.Dw j) w.n) T'.Fr)
          (g : Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)),
          P' ∈ FFV (Dw := T.Q.Dw j) T' (wtA w) w.n ∧ (∀ b, IsIntPS T' (g b)) ∧
          letI := io'.toAlgebra
          nval Tc.V e (evI yI f) = nval T'.V e' (∑ mo ∈ P'.support, P'.coeff mo *
            ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 (T.Q.l.M ^ 2) (g b) C.ch.uvec
              (MvPolynomial.monomial (colOf mo b) 1))

theorem coprime_of_mod_one {g p : ℕ} (h : g % p = 1) : Nat.Coprime g p := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem g_coprime_ram (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  apply coprime_of_mod_one
  rcases hp with rfl | rfl | rfl
  · have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ D.host.QS * D.host.q * D.host.d from
      (h2.mul_right _).mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.q, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem M_not_mem_of_ram (D : D7) (T : Top D) (h : LawsP T) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (p : ℕ)
    (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal) :
    ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := by
  intro hmem
  rw [h.toLawsCore.pins.2.1.1, Nat.cast_mul] at hmem
  rcases la.isPrime.mem_or_mem hmem with h0 | h1
  · exact Pf.not_both_mem la (g_coprime_ram D 0 p hp) h0 hpl
  · exact Pf.not_both_mem la (g_coprime_ram D 1 p hp) h1 hpl

theorem differentExponent_nonneg (D : D7) (p : ℕ) : 0 ≤ vdP D p := by
  unfold vdP
  split_ifs
  · have h1 : (2⁻¹ : ℝ) ^ D.R.e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ D.R.e := Nat.cast_nonneg _
    linarith
  · norm_num

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 f i ≤ ∑ i, f i := by
  unfold ext0
  have e1 : ∑ i : Fin m, (if h : (i : ℕ) < p then f ⟨i, h⟩ else 0) =
      ∑ i ∈ Finset.range m, (if h : i < p then f ⟨i, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) m
  have e2 : ∑ i : Fin p, f i = ∑ i ∈ Finset.range p, (if h : i < p then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  rw [e1, e2, ← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun i => i < p)]
  have e3 : ∑ i ∈ (Finset.range m).filter (fun i => ¬ i < p), (if h : i < p then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => dif_neg (Finset.mem_filter.mp hi).2
  rw [e3, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) (fun _ _ _ => Nat.zero_le _)

open Classical in

theorem DF_wtA_le {D : D7} (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ Formalism.MainNotions.WeightAlgebra.DF w := by
  show ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) ≤
    ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i)
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = conjEmb (DV.tauEmb D t) then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact add_le_add (sum_extendByZero_le_sum _ _) (sum_extendByZero_le_sum _ _)

theorem ramifiedValue_of_chartValues (hVC : HarmonicValueAtIntegralPoint) (hCR : ChartValueBoundRamified) : ChartValueRamified := by
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy p hp hpl _C
  have hM := M_not_mem_of_ram D T h la p hp hpl
  obtain ⟨T', io', e', yI', ho', hy', C, P', g, hP', hg, hval⟩ :=
    hVC D T h j hj nab hnab w x P hP f hf Tc io yI e la ho hy hM
  rw [hval]
  refine le_trans ?_ (hCR D T h j hj hnab.1 T' io' yI' e' la ho' hy' p hp hpl C (T.Q.l.M ^ 2) (wtA w) w.n P' hP' g hg)
  apply EReal.coe_le_coe_iff.2
  have hv : (0 : ℝ) ≤ ((vLa la (p : T.Q.c.F) : ℤ) : ℝ) := by exact_mod_cast Pf.vLa_nat_nonneg la p
  have hvd : 0 ≤ vdP D p := differentExponent_nonneg D p
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast DF_wtA_le T j w
  have hvv := mul_nonneg hv hvd
  nlinarith

theorem integralValue_of_chartValues (hVC : HarmonicValueAtIntegralPoint) (hCI : ChartValueIntegralGood) : ChartValueUnramified := by
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy hbad _C
  have hM : ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := by
    intro hmem
    rw [h.toLawsCore.pins.2.1.1, Nat.cast_mul] at hmem
    rcases la.isPrime.mem_or_mem hmem with h0 | h1
    · exact hbad (D.host.g 0) (by simp) h0
    · exact hbad (D.host.g 1) (by simp) h1
  obtain ⟨T', io', e', yI', ho', hy', C, P', g, hP', hg, hval⟩ :=
    hVC D T h j hj nab hnab w x P hP f hf Tc io yI e la ho hy hM
  rw [hval]
  exact hCI D T h j hj hnab.1 T' io' yI' e' la ho' hy'
    (fun p hp => hbad p (by simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢; tauto)) C (T.Q.l.M ^ 2) (wtA w) w.n P' hP' g hg

end ReciprocityTheory.ChartRestriction.G.PullbackSections
