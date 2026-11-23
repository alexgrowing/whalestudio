import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerClosedness

private theorem q_iff {K : Type} [Field K] (m : ℕ) (a b : PowerSeries K) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) a = Ideal.Quotient.mk _ b ↔
      ∀ d < m, PowerSeries.coeff d a = PowerSeries.coeff d b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

private theorem ulim_A {K : Type} [Field K] [Finite K] (U : Ultrafilter ℕ) (a : ℕ → PowerSeries K) :
    ∃ b : PowerSeries K, ∀ m, ∀ᶠ N in (U : Filter ℕ),
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) (a N) = Ideal.Quotient.mk _ b := by
  classical
  have hv : ∀ d, ∃ v : K, ∀ᶠ N in (U : Filter ℕ), PowerSeries.coeff d (a N) = v := by
    intro d
    obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map fun N => PowerSeries.coeff d (a N))
    refine ⟨v, ?_⟩
    have hmem : ({v} : Set K) ∈ (U.map fun N => PowerSeries.coeff d (a N)) := by
      rw [hv, Ultrafilter.mem_pure]
      exact Set.mem_singleton v
    exact Ultrafilter.mem_map.mp hmem
  choose v hv using hv
  refine ⟨PowerSeries.mk v, fun m => ?_⟩
  have hall : ∀ᶠ N in (U : Filter ℕ), ∀ d ∈ Finset.range m, PowerSeries.coeff d (a N) = v d :=
    (Filter.eventually_all_finset _).mpr (fun d _ => hv d)
  filter_upwards [hall] with N hN
  rw [q_iff]
  intro d hd
  rw [PowerSeries.coeff_mk]
  exact hN d (Finset.mem_range.mpr hd)

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

private theorem q_mono {m N : ℕ} (h : m ≤ N) {a b : x.A}
    (e : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) a = Ideal.Quotient.mk _ b) :
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq] at e ⊢
  exact (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h)) e

private theorem q_sep {a b : x.A}
    (e : ∀ m, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ b) : a = b :=
  PowerSeries.ext fun d => (q_iff (d + 1) a b).1 (e _) d (Nat.lt_succ_self d)

private theorem red_iff (g m : ℕ) (a b : DD x.A g) : x.redD g m a = x.redD g m b ↔
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.a = Ideal.Quotient.mk _ b.a ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep j) = Ideal.Quotient.mk _ (b.ep j)) ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep' j) = Ideal.Quotient.mk _ (b.ep' j)) ∧
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.eta = Ideal.Quotient.mk _ b.eta := by
  constructor
  · intro e
    exact ⟨congrArg DD.a e, fun j => congrFun (congrArg DD.ep e) j,
      fun j => congrFun (congrArg DD.ep' e) j, congrArg DD.eta e⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact DD.ext h1 (funext h2) (funext h3) h4

private theorem red_mono {g m N : ℕ} (h : m ≤ N) {a b : DD x.A g} (e : x.redD g N a = x.redD g N b) :
    x.redD g m a = x.redD g m b := by
  rw [red_iff] at e ⊢
  obtain ⟨h1, h2, h3, h4⟩ := e
  exact ⟨q_mono x h h1, fun j => q_mono x h (h2 j), fun j => q_mono x h (h3 j), q_mono x h h4⟩

private theorem red_sep {g : ℕ} {a b : DD x.A g} (e : ∀ m, x.redD g m a = x.redD g m b) : a = b := by
  refine DD.ext ?_ ?_ ?_ ?_
  · exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).1
  · funext j
    exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.1 j
  · funext j
    exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.2.1 j
  · exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.2.2

private theorem red_surj (g m : ℕ) : Function.Surjective (x.redD g m) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.a
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective y.eta
  choose e1 he1 using fun j => Ideal.Quotient.mk_surjective (y.ep j)
  choose e2 he2 using fun j => Ideal.Quotient.mk_surjective (y.ep' j)
  exact ⟨⟨a, e1, e2, t⟩, DD.ext ha (funext he1) (funext he2) ht⟩

private theorem dd_components_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) :
    (c • y).a = c * y.a ∧ (c • y).ep = c • y.ep ∧ (c • y).ep' = c • y.ep' ∧ (c • y).eta = c * y.eta := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext j
    show c * y.ep j + 0 * y.a = c * y.ep j
    ring
  · funext j
    show c * y.ep' j + 0 * y.a = c * y.ep' j
    ring
  · show c * y.eta + 0 * y.a + ∑ j, (0 * y.ep' j + 0 * y.ep j) = c * y.eta
    simp

private theorem red_ker {g m : ℕ} {a b : DD x.A g} (e : x.redD g m a = x.redD g m b) :
    a - b ∈ Ideal.span {algebraMap x.A (DD x.A g) x.t} ^ m := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton']
  obtain ⟨h1, h2, h3, h4⟩ := (red_iff x g m a b).mp e
  have hc : ∀ u v : x.A, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) u = Ideal.Quotient.mk _ v →
      ∃ w, u - v = x.t ^ m * w := by
    intro u v huv
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at huv
    exact huv
  obtain ⟨w1, hw1⟩ := hc _ _ h1
  obtain ⟨w4, hw4⟩ := hc _ _ h4
  choose w2 hw2 using fun j => hc _ _ (h2 j)
  choose w3 hw3 using fun j => hc _ _ (h3 j)
  refine ⟨⟨w1, w2, w3, w4⟩, ?_⟩
  rw [mul_comm, ← Algebra.smul_def]
  obtain ⟨s1, s2, s3, s4⟩ := dd_components_smul (x.t ^ m) (⟨w1, w2, w3, w4⟩ : DD x.A g)
  refine DD.ext ?_ ?_ ?_ ?_
  · rw [s1]
    exact hw1.symm
  · rw [s2]
    funext j
    exact (hw2 j).symm
  · rw [s3]
    funext j
    exact (hw3 j).symm
  · rw [s4]
    exact hw4.symm

private theorem pow_bot (g m : ℕ) : Ideal.span {algebraMap x.A (DD (x.Am m) g) x.t} ^ m = ⊥ := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.span_singleton_eq_bot]
  show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
  rw [Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]

private theorem ulim_D (g : ℕ) (U : Ultrafilter ℕ) (a : ℕ → DD x.A g) :
    ∃ b : DD x.A g, ∀ m, ∀ᶠ N in (U : Filter ℕ), x.redD g m (a N) = x.redD g m b := by
  obtain ⟨ba, hba⟩ := ulim_A U (fun N => (a N).a)
  obtain ⟨bt, hbt⟩ := ulim_A U (fun N => (a N).eta)
  choose b1 hb1 using fun j => ulim_A U (fun N => (a N).ep j)
  choose b2 hb2 using fun j => ulim_A U (fun N => (a N).ep' j)
  refine ⟨⟨ba, b1, b2, bt⟩, fun m => ?_⟩
  filter_upwards [hba m, hbt m, Filter.eventually_all.mpr (fun j => hb1 j m),
    Filter.eventually_all.mpr (fun j => hb2 j m)] with N h1 h4 h2 h3
  rw [red_iff]
  exact ⟨h1, h2, h3, h4⟩

private theorem part_of (g : ℕ) (b1 b2 b3 b4 : Bool) (y : DD x.A g)
    (h : ∀ m, ∃ N y', m ≤ N ∧ x.redD g m y = x.redD g m y' ∧ x.redD g N y' ∈ ddPart x.A (x.Am N) g b1 b2 b3 b4) :
    y ∈ ddPart x.A x.A g b1 b2 b3 b4 := by
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).1
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) y'.a = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact hp.1 hb
    rw [h1]
    exact q_mono x hmN h2
  · funext j
    show y.ep j = 0
    apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.1 j
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) (y'.ep j) = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact congrFun (hp.2.1 hb) j
    rw [h1]
    exact q_mono x hmN h2
  · funext j
    show y.ep' j = 0
    apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.2.1 j
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) (y'.ep' j) = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact congrFun (hp.2.2.1 hb) j
    rw [h1]
    exact q_mono x hmN h2
  · apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.2.2
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) y'.eta = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact hp.2.2.2 hb
    rw [h1]
    exact q_mono x hmN h2

private theorem mem_second_order_of_reductions (g : ℕ) (Y : Matrix (Fin n) (Fin n) (DD x.A g))
    (h : ∀ m, ∃ (N : ℕ) (Y' : Matrix (Fin n) (Fin n) (DD x.A g)), m ≤ N ∧ Y.map (x.redD g m) = Y'.map (x.redD g m) ∧
      Y'.map (x.redD g N) ∈ W2 n x.A (x.Am N) g x.a) :
    Y ∈ W2 n x.A x.A g x.a := by
  intro i j
  refine ⟨fun e => part_of x g _ _ _ _ _ fun m => ?_, fun e => part_of x g _ _ _ _ _ fun m => ?_⟩
  · obtain ⟨N, Y', hN, h1, h2⟩ := h m
    exact ⟨N, Y' i j, hN, congrFun (congrFun h1 i) j, (h2 i j).1 e⟩
  · obtain ⟨N, Y', hN, h1, h2⟩ := h m
    exact ⟨N, Y' i j, hN, congrFun (congrFun h1 i) j, (h2 i j).2 e⟩

variable {x} (k : Kap x) (m : ℕ)

private theorem map_ep (Z : Fin k.g → Matrix (Fin n) (Fin n) x.A) :
    (x.redD k.g m).mapMatrix (DD.epM fun j => (Z j).map (algebraMap x.A x.A)) =
      DD.epM fun j => (Z j).map (algebraMap x.A (x.Am m)) := by
  ext a b <;> simp [DD.epM, DD.map]

private theorem map_al (Z : Matrix (Fin n) (Fin n) x.A) :
    (x.redD k.g m).mapMatrix (Z.map (algebraMap x.A (DD x.A k.g))) = Z.map (algebraMap x.A (DD (x.Am m) k.g)) := by
  rw [AlgHom.mapMatrix_apply, Matrix.map_map]
  congr 1

private theorem map_ρ1 (g : F.G₀) : (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = k.ρ1 (x.Am m) g := by
  unfold Kap.ρ1 NP.ρX
  rw [map_mul, map_add, map_one, map_ep, map_al]

private theorem map_weyl_lift_reduction (v : F.Vl) : (x.redD k.g m).mapMatrix (k.w1 x.A v) = k.w1 (x.Am m) v := by
  unfold Kap.w1 NP.wX
  rw [map_mul, map_sub, map_one, map_ep, map_al]

private theorem map_inverse_weyl_lift_reduction (v : F.Vl) : (x.redD k.g m).mapMatrix (k.wi1 x.A v) = k.wi1 (x.Am m) v := by
  unfold Kap.wi1 NP.wiX
  rw [map_mul, map_add, map_one, map_ep, map_al]

private theorem mat_sep {Y Z : Matrix (Fin n) (Fin n) (DD x.A k.g)}
    (e : ∀ m, (x.redD k.g m).mapMatrix Y = (x.redD k.g m).mapMatrix Z) : Y = Z := by
  funext i j
  exact red_sep x fun m => congrFun (congrFun (e m) i) j

end UpperTheory.V.Pa.SelmerClosedness

open UpperTheory.V.Pa.SelmerClosedness in
theorem UpperTheory.V.Pa.selmer_second_closed_under_limits :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (z : G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), (∀ m, (fun g => (z g).map (x.redD k.g m)) ∈ Sel2 h (x.Am m) k) → z ∈ Sel2 h x.A k := by
  intro l _ L G G0 h n x k z hyp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    apply mem_second_order_of_reductions x k.g (z g)
    intro m
    obtain ⟨hW, -⟩ := hyp m
    exact ⟨m, z g, le_rfl, rfl, hW g⟩
  · intro i j N
    obtain ⟨-, hA, -⟩ := hyp N
    have hl := hA i j N
    have hf : IsLocallyConstant fun g => x.redD k.g N (z g i j) := by
      refine IsLocallyConstant.desc _ _ hl (fun a b hab => ?_)
      rw [Ideal.Quotient.eq, pow_bot, Ideal.mem_bot, sub_eq_zero] at hab
      exact hab
    let s := Function.surjInv (red_surj x k.g N)
    have hcomp : (fun g => Ideal.Quotient.mk (Ideal.span {algebraMap x.A (DD x.A k.g) x.t} ^ N) (z g i j)) =
        (fun y => Ideal.Quotient.mk (Ideal.span {algebraMap x.A (DD x.A k.g) x.t} ^ N) (s y)) ∘
          (fun g => x.redD k.g N (z g i j)) := by
      funext g
      simp only [Function.comp]
      rw [Ideal.Quotient.eq]
      exact red_ker x (Function.surjInv_eq (red_surj x k.g N) _).symm
    rw [hcomp]
    exact hf.comp _
  · intro g g'
    beta_reduce
    apply mat_sep k
    intro m
    obtain ⟨-, -, hc, -⟩ := hyp m
    rw [map_add, map_mul, map_mul, map_ρ1, map_ρ1]
    exact hc g g'
  · intro g
    apply mat_sep k
    intro m
    obtain ⟨-, -, -, hconj, -⟩ := hyp m
    have e := hconj g
    funext a b
    have e' := congrFun (congrFun e a) b
    simp at e' ⊢
    exact e'
  · intro u g hg
    apply mat_sep k
    intro m
    obtain ⟨-, -, -, -, hI, -⟩ := hyp m
    rw [map_zero]
    exact hI u g hg
  · intro v
    have hYm : ∀ m, ∃ Y : Matrix (Fin n) (Fin n) (DD x.A k.g),
        (x.redD k.g m).mapMatrix Y ∈ W2 n x.A (x.Am m) k.g x.a ∧
        LocAt G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (k.w1 (x.Am m)) (k.wi1 (x.Am m))
          (fun g => (z g).map (x.redD k.g m)) v ((x.redD k.g m).mapMatrix Y) := by
      intro m
      obtain ⟨-, -, -, -, -, hL⟩ := hyp m
      obtain ⟨Y0, hY0W, hY0L⟩ := hL v
      choose Yl hYl using fun a b => red_surj x k.g m (Y0 a b)
      have hY0 : (x.redD k.g m).mapMatrix (Matrix.of Yl) = Y0 := by
        funext a b
        exact hYl a b
      refine ⟨Matrix.of Yl, ?_, ?_⟩
      · rw [hY0]
        exact hY0W
      · rw [hY0]
        exact hY0L
    choose Yt hYtW hYtL using hYm
    let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
    choose Y hY using fun a b => ulim_D x k.g U (fun N => Yt N a b)
    have hev : ∀ m, ∃ N, m ≤ N ∧
        (x.redD k.g m).mapMatrix (Matrix.of Y) = (x.redD k.g m).mapMatrix (Yt N) := by
      intro m
      have h1 : ∀ᶠ N in (U : Filter ℕ), ∀ a b, x.redD k.g m (Yt N a b) = x.redD k.g m (Y a b) :=
        Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => hY a b m
      have h2 : ∀ᶠ N in (U : Filter ℕ), m ≤ N := by
        apply Filter.Eventually.filter_mono Filter.hyperfilter_le_cofinite
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_ge_atTop m
      obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
      refine ⟨N, hN2, ?_⟩
      funext a b
      exact (hN1 a b).symm
    refine ⟨Matrix.of Y, ?_, ?_⟩
    · apply mem_second_order_of_reductions x k.g
      intro m
      obtain ⟨N, hmN, e⟩ := hev m
      exact ⟨N, Yt N, hmN, e, hYtW N⟩
    · intro g
      let E : Matrix (Fin n) (Fin n) (DD x.A k.g) → Matrix (Fin n) (Fin n) (DD x.A k.g) := fun Y1 =>
        k.wi1 x.A v * (z ((G.frame.φ v) g) -
          dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y1 ((G.frame.φ v) g)) * k.w1 x.A v
      have hE : ∀ m (Y1 : Matrix (Fin n) (Fin n) (DD x.A k.g)), (x.redD k.g m).mapMatrix (E Y1) =
          k.wi1 (x.Am m) v * ((z ((G.frame.φ v) g)).map (x.redD k.g m) -
            dY G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) ((x.redD k.g m).mapMatrix Y1) ((G.frame.φ v) g)) *
              k.w1 (x.Am m) v := by
        intro m Y1
        simp only [E, dY]
        rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_ρ1, map_ρ1, map_weyl_lift_reduction, map_inverse_weyl_lift_reduction]
        rfl
      have hent : ∀ i j, (∀ N, (k.wi1 (x.Am N) v * ((z ((G.frame.φ v) g)).map (x.redD k.g N) -
            dY G.frame (fun g => k.ρ1 (x.Am N) (h.p₀ g)) ((x.redD k.g N).mapMatrix (Yt N)) ((G.frame.φ v) g)) *
              k.w1 (x.Am N) v) i j = 0) → E (Matrix.of Y) i j = 0 := by
        intro i j h0
        apply red_sep x
        intro m
        obtain ⟨N, hmN, e⟩ := hev m
        have e1 := congrFun (congrFun (hE m (Matrix.of Y)) i) j
        have e2 := congrFun (congrFun (hE m (Yt N)) i) j
        have e3 := congrFun (congrFun (hE N (Yt N)) i) j
        rw [e] at e1
        have e4 : x.redD k.g m (E (Matrix.of Y) i j) = x.redD k.g m (E (Yt N) i j) :=
          e1.trans e2.symm
        rw [e4, map_zero]
        have e5 : x.redD k.g N (E (Yt N) i j) = x.redD k.g N 0 := by
          rw [map_zero]
          exact e3.trans (h0 N)
        rw [red_mono x hmN e5, map_zero]
      exact ⟨fun i j hij => hent i j (fun N => (hYtL N g).1 i j hij),
        fun hg i => hent i i (fun N => (hYtL N g).2 hg i)⟩
