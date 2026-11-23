import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.InChartSt

set_option autoImplicit false

noncomputable section

open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

theorem nilSt : NilSt := by
  intro p hp C _ _ v O _ _ hv _ hpu c hc n
  have hunit : ∀ x : O, ¬ IsUnit x → v (algebraMap O C x) < 1 := by
    intro x hx
    refine lt_of_le_of_ne (hv.map_le_one x) ?_
    intro h1
    apply hx
    refine hv.isUnit_of_one ?_ h1
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hc1 : v (algebraMap O C c) < 1 := by
    apply hunit c
    intro hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ hc hu)
  have hp0 : 0 < v (algebraMap O C ((p : O) ^ n)) := by
    rw [map_pow, map_pow, map_natCast]
    apply pow_pos
    rw [pos_iff_ne_zero, Ne, Valuation.zero_iff]
    exact Nat.cast_ne_zero.mpr hp
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hp0 hc1
  refine ⟨N, Ideal.mem_span_singleton.mpr (hv.dvd_of_le ?_)⟩
  have e : v (algebraMap O C (c ^ N)) = v (algebraMap O C c) ^ N := by
    rw [map_pow, map_pow]
  rw [e]
  exact hN.le

theorem jetSt : JetSt := by
  intro T B _ _ _ κ _ b hb
  have hmem : ∀ j, b j ∈ Ideal.span (Set.range b) := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hnil : IsNilpotent (Ideal.span (Set.range b)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range b))]
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact mem_nilradical.mpr (hb j)
  obtain ⟨K, hK⟩ := hnil
  refine ⟨K, fun k hk => ?_⟩
  have hJk : Ideal.span (Set.range b) ^ (k + 1) = ⊥ := by
    apply le_bot_iff.mp
    calc Ideal.span (Set.range b) ^ (k + 1) ≤ Ideal.span (Set.range b) ^ K :=
          Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [hK, Ideal.zero_eq_bot]
  refine ⟨jetLift T _ hJk b hmem, fun j => jetLift_zR _ hJk b hmem j, ?_⟩
  intro ψ hψ
  apply jet_ext
  intro j
  rw [hψ j, jetLift_zR]

theorem evalSt : EvalSt := by
  intro T O _ _ _ I m d k χ c hχ f
  have htr : MvPowerSeries.trunc O (Finsupp.equivFunOnFinite.symm fun _ => k + 1)
      (MvPowerSeries.map (algebraMap T O) f) = MvPolynomial.map (algebraMap T O)
        (MvPowerSeries.trunc T (Finsupp.equivFunOnFinite.symm fun _ => k + 1) f) := by
    ext e
    simp only [MvPolynomial.coeff_map, MvPowerSeries.coeff_trunc]
    split_ifs <;> simp
  have hcomp : χ.comp (Ideal.Quotient.mkₐ T _) =
      (Ideal.Quotient.mkₐ T I).comp (MvPolynomial.aeval (fun q : Fin m × Fin d => c q.1 q.2)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.aeval_X]
    exact hχ q
  rw [htr, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
  exact AlgHom.congr_fun hcomp _

theorem smod_iff {O : Type} [CommRing O] (p : O) (n : ℕ) (u w : O) :
    u ≡ w [SMOD ((Ideal.span {p}) ^ n • ⊤ : Submodule O O)] ↔
      Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w := by
  have h : ((Ideal.span {p}) ^ n • ⊤ : Submodule O O) = Ideal.span {p ^ n} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rw [SModEq.sub_mem, Ideal.Quotient.eq, h]

theorem eq_of_mod {O : Type} [CommRing O] (p : O) (hH : IsHausdorff (Ideal.span {p}) O) (u w : O)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w) : u = w := by
  refine sub_eq_zero.mp (hH.haus (u - w) fun n => (smod_iff p n (u - w) 0).mpr ?_)
  rw [map_sub, map_zero, h n, sub_self]

theorem sepSt : SepSt := by
  intro T A O _ _ _ _ _ p hH h h' H
  ext z
  refine eq_of_mod p hH (h z) (h' z) fun n => ?_
  have := AlgHom.congr_fun (H n) z
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using this

theorem algLimSt : AlgLimSt := by
  intro T A O _ _ _ _ _ p hC a hc
  have hdown : ∀ z : A, ∀ m n : ℕ, m ≤ n → ∀ y : O,
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z →
        Ideal.Quotient.mk (Ideal.span {p ^ m}) y = a m z := by
    intro z m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun y hy => hy
    | succ n _ ih => exact fun y hy => ih y (hc n z y hy)
  have hlim : ∀ z : A, ∃ L : O, ∀ n, Ideal.Quotient.mk (Ideal.span {p ^ n}) L = a n z := by
    intro z
    have hs : ∀ n, ∃ y : O, Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z :=
      fun n => Ideal.Quotient.mk_surjective (a n z)
    choose y hy using hs
    obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec' y (fun {m n} hmn =>
      (smod_iff p m (y m) (y n)).mpr (by rw [hy m, hdown z m n hmn (y n) (hy n)]))
    exact ⟨L, fun n => by rw [← (smod_iff p n (y n) L).mp (hL n), hy n]⟩
  choose L hL using hlim
  have huniq : ∀ x y : O, (∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) x =
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y) → x = y :=
    fun x y H => eq_of_mod p hC.toIsHausdorff x y H
  refine ⟨
    { toFun := L
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }, ?_⟩
  · exact huniq _ _ fun n => by simp only [hL, map_one]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_mul]
  · exact huniq _ _ fun n => by simp only [hL, map_zero]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_add]
  · intro t
    refine huniq _ _ fun n => ?_
    rw [hL, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).commutes t).symm
  · intro n
    ext z
    exact hL z n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
