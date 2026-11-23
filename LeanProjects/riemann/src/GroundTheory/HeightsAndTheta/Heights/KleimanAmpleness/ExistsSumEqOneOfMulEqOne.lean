import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem locIn_eq_of_le_powMulMem {A B : Subalgebra S Ω} (hAB : A ≤ B) {e : Ω} (he : e ∈ A)
    (hB : B ≤ powMulMem A e he) (P : Ideal B) (hP : P.IsPrime) (heP : (⟨e, hAB he⟩ : B) ∉ P) :
    IndefiniteRowSideFullHecke.Kleiman2.locIn B P = IndefiniteRowSideFullHecke.Kleiman2.locIn A (P.comap (Subalgebra.inclusion hAB)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    have h0 : (⟨0, hAB he⟩ : B) = 0 := rfl
    exact heP (h0 ▸ P.zero_mem)
  have hpow : ∀ M : ℕ, (⟨e, hAB he⟩ : B) ^ M ∉ P := fun M h => heP (hP.mem_of_pow_mem M h)
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    obtain ⟨K, hK⟩ := hB a.2
    obtain ⟨K', hK'⟩ := hB b.2
    have ha' : e ^ (K + K') * a ∈ A := by
      rw [pow_add, mul_comm (e ^ K), mul_assoc]; exact A.mul_mem (A.pow_mem he _) hK
    have hb' : e ^ (K + K') * b ∈ A := by
      rw [pow_add, mul_assoc]; exact A.mul_mem (A.pow_mem he _) hK'
    refine Subring.subset_closure ⟨⟨_, ha'⟩, ⟨_, hb'⟩, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      intro h
      have h' : (⟨e, hAB he⟩ : B) ^ (K + K') * b ∈ P := by
        convert h using 1
        apply Subtype.ext
        simp
      rcases hP.mem_or_mem h' with h1 | h1
      · exact hpow _ h1
      · exact hb h1
    · simp only
      rw [mul_div_mul_left _ _ (pow_ne_zero _ he0)]
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩

theorem exists_isPrime_locIn_eq {A B : Subalgebra S Ω} (hAB : A ≤ B) {e : Ω} (he : e ∈ A)
    (hB : B ≤ powMulMem A e he) (p : Ideal A) (hp : p.IsPrime) (hep : (⟨e, he⟩ : A) ∉ p) :
    ∃ P : Ideal B, P.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn B P = IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  have hpow : ∀ M : ℕ, (⟨e, he⟩ : A) ^ M ∉ p := fun M h => hep (hp.mem_of_pow_mem M h)
  let P : Ideal B :=
    { carrier := {b | ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω)}
      add_mem' := by
        rintro b b' ⟨M, a, ha, hab⟩ ⟨M', a', ha', hab'⟩
        refine ⟨M + M', ⟨e, he⟩ ^ M' * a + ⟨e, he⟩ ^ M * a',
          p.add_mem (p.mul_mem_left _ ha) (p.mul_mem_left _ ha'), ?_⟩
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul, SubmonoidClass.coe_pow]
        rw [← hab, ← hab']
        ring
      zero_mem' := ⟨0, 0, p.zero_mem, by simp⟩
      smul_mem' := by
        rintro c b ⟨M, a, ha, hab⟩
        obtain ⟨K, hK⟩ := hB c.2
        refine ⟨K + M, ⟨_, hK⟩ * a, p.mul_mem_left _ ha, ?_⟩
        simp only [smul_eq_mul, Subalgebra.coe_mul]
        rw [← hab]
        ring }
  have hmemP : ∀ b : B, b ∈ P ↔ ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω) := fun _ => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmemP]
      rintro ⟨M, a, ha, hab⟩
      apply hpow M
      convert ha using 1
      exact Subtype.ext (by simpa using hab)
    · intro b b' hbb
      obtain ⟨M, a, ha, hab⟩ := (hmemP _).mp hbb
      obtain ⟨K, hK⟩ := hB b.2
      obtain ⟨K', hK'⟩ := hB b'.2
      have h1 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) = ⟨e, he⟩ ^ (K + K') * a := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow]
        rw [← hab]
        simp only [Subalgebra.coe_mul]
        ring
      have h2 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) ∈ p := by
        rw [h1]; exact p.mul_mem_left _ ha
      rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 (hpow M)
      rcases hp.mem_or_mem h3 with h4 | h4
      · exact Or.inl ⟨K, _, h4, rfl⟩
      · exact Or.inr ⟨K', _, h4, rfl⟩
  have heP : (⟨e, hAB he⟩ : B) ∉ P := by
    rintro ⟨M, a, ha, hab⟩
    apply hpow (M + 1)
    convert ha using 1
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [← hab, pow_succ]
  have hcomap : P.comap (Subalgebra.inclusion hAB) = p := by
    ext a
    rw [Ideal.mem_comap]
    constructor
    · rintro ⟨M, a', ha', hab⟩
      have h1 : (⟨e, he⟩ : A) ^ M * a = a' := by
        apply Subtype.ext
        simpa using hab
      have h2 : (⟨e, he⟩ : A) ^ M * a ∈ p := by rw [h1]; exact ha'
      rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 (hpow M)
      · exact h3
    · intro ha
      exact ⟨0, a, ha, by simp⟩
  refine ⟨P, hPprime, ?_⟩
  rw [locIn_eq_of_le_powMulMem hAB he hB P hPprime heP, hcomap]

theorem exists_sum_eq_one_of_mul_eq_one (A : Subalgebra S Ω) (Q' : Submodule A Ω) {m : ℕ} (g : Fin m → Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) :
    ∃ w : Fin m → Ω, (∀ a b, g a * w b ∈ A) ∧ ∑ b, g b * w b = 1 := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  refine ⟨w, fun a b => ?_, hsum⟩
  have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
    (hwQ b)
  rw [hQQ, Submodule.mem_one] at h
  obtain ⟨y, hy⟩ := h
  rw [← hy]
  exact y.2

end Loc

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem span_graphGens_eq (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) :
    Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hi)) (Set.range fun b => x i ^ (-n) * s b) =
      Q.sub (Kleiman.singleChart hi) := by
  set I := Kleiman.singleChart hi with hIdef
  have hiI : i ∈ I.1 := Finset.mem_singleton_self i
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I := by
      rw [← hgen I]; exact Submodule.subset_span ⟨b, rfl⟩
    obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb
    have : x i ^ (-n) * s b = y := by
      rw [hyb, smul_eq_mul, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]
    show x i ^ (-n) * s b ∈ Q.sub I
    rw [this]
    exact hy
  · intro y hy
    have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s) := by
      rw [hgen I]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha ⊢
    have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ha, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]

theorem exists_graph_inverse (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ∃ w : Fin m → Ω, (∀ a b, x i ^ (-n) * s a * w b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ∧
      ∑ b, x i ^ (-n) * s b * w b = 1 := by
  obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← span_graphGens_eq Q n s hgen hi] at hQ'
  obtain ⟨w, hw, hsum⟩ := exists_sum_eq_one_of_mul_eq_one _ Q' _ hQ'
  refine ⟨w, fun a b => ?_, hsum⟩
  rw [chartRingOver_oneBlock x (fun _ => i) hi]
  exact hw a b

theorem graphRing_between {i : Fin (N + 1)} (hi : x i ≠ 0) (n : ℤ) (s : Fin m → Ω) (w : Fin m → Ω)
    (hw : ∀ a b, x i ^ (-n) * s a * w b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i))
    {j : Fin m} (hj : s j ≠ 0) (b : Fin m) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) ≤ graphRing S x s i j ∧
      graphRing S x s i j ≤ powMulMem _ _ (hw j b) := by
  have hA := chartRingOver_oneBlock (S := S) x (fun _ => i) hi
  refine ⟨?_, ?_⟩
  · rw [hA]; exact chartRing_le_graphRing x s hi j
  · refine graphRing_le x s hi j _ (fun a ha => ⟨0, ?_⟩) fun c => ⟨1, ?_⟩
    · rw [pow_zero, one_mul, hA]; exact ha
    · have : (x i ^ (-n) * s j * w b) ^ 1 * (s c / s j) = x i ^ (-n) * s c * w b := by
        field_simp
      rw [this]
      exact hw c b

end Graph

theorem GraphModel.full : GraphModel.Statement := by
  intro S _ N Ω _ _ x Q n m s hx hgen
  obtain ⟨i₀, hi₀⟩ := hx
  refine ⟨?_, ?_⟩
  · rintro (⟨⟩ | ⟨⟩)
    · exact ⟨i₀, hi₀⟩
    · obtain ⟨w, -, hsum⟩ := exists_graph_inverse Q n s hgen hi₀
      by_contra h
      push Not at h
      have h0 : ∀ b, s b = 0 := fun b => h b
      simp [h0] at hsum
  · show IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)
    ext z
    constructor
    · rintro ⟨c, hc, P, hP, rfl⟩
      obtain ⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j :=
        ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
      have hi : x i ≠ 0 := hc (Sum.inl ())
      have hj : s j ≠ 0 := hc (Sum.inr ())
      obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
      have hB : ∀ b, chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) ≤ graphRing S x s i j ∧
          graphRing S x s i j ≤ powMulMem _ _ (hw j b) := graphRing_between hi n s w hw hj
      obtain ⟨hAB, -⟩ := hB j
      obtain ⟨b, hb⟩ : ∃ b, (⟨_, hAB (hw j b)⟩ : graphRing S x s i j) ∉ P := by
        by_contra h
        push Not at h
        apply hP.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : graphRing S x s i j) =
            ∑ b, (⟨s b / s j, div_mem_graphRing_inr x s i j b⟩ : graphRing S x s i j) * ⟨_, hAB (hw j b)⟩ := by
          apply Subtype.ext
          simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
          rw [← hsum]
          refine Finset.sum_congr rfl fun b _ => ?_
          field_simp
        rw [h1]
        exact Ideal.sum_mem _ fun b _ => P.mul_mem_left _ (h b)
      obtain ⟨hAB', hle⟩ := hB b
      have hP' : (P.comap (Subalgebra.inclusion hAB')).IsPrime := Ideal.comap_isPrime _ _
      refine ⟨fun _ => i, fun _ => hi, _, hP', ?_⟩
      exact locIn_eq_of_le_powMulMem hAB' (hw j b) hle P hP hb
    · rintro ⟨c, hc, p, hp, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Fin (N + 1), c = fun _ => i := ⟨c (), funext fun u => rfl⟩
      have hi : x i ≠ 0 := hc ()
      obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
      obtain ⟨j, hj⟩ : ∃ j, (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ∉ p := by
        by_contra h
        push Not at h
        apply hp.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = ∑ b, ⟨_, hw b b⟩ := by
          apply Subtype.ext
          simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum]
          exact hsum.symm
        rw [h1]
        exact Ideal.sum_mem _ fun b _ => h b
      have hsj : s j ≠ 0 := by
        intro h0
        apply hj
        have : (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = 0 :=
          Subtype.ext (by simp [h0])
        rw [this]
        exact p.zero_mem
      obtain ⟨hAB, hle⟩ := graphRing_between hi n s w hw hsj j
      obtain ⟨P, hP, hPeq⟩ := exists_isPrime_locIn_eq hAB (hw j j) hle p hp hj
      refine ⟨graphChart i j, ?_, P, hP, hPeq.symm⟩
      rintro (⟨⟩ | ⟨⟩)
      · exact hi
      · exact hsj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
