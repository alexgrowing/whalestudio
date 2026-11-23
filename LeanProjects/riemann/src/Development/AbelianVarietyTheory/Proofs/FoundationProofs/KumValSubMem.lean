import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqTrue
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RecipConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.LocGlue

open GlobalTheory.LambdaValuationPowers.HTCoUniq ReciprocityTheory.Neutral.Cmp

theorem uniq_fix : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₂ : ℕ, ∀ (m : ℕ) (D : Qbar l) (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω),
    (∀ i, ‖o i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) →
    (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m (D * GlobalTheory.LambdaValuationPowers.lamv l m s) (∑ i, o i * (j (s (w i)) - j (w i)))) →
    Cg (m - c₂) D 0 := by
  intro l _ hl2 Ω _ _ _ A c j _ hj
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  obtain ⟨c', hc'⟩ := uniq_true hl2
  obtain ⟨c₁, hc₁⟩ := core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha)
    (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ))
    natCast_ne_zero hp1 c'
  refine ⟨c₁, ?_⟩
  intro m D q o w how hyp
  have hx : ‖∑ i, o i * j (w i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (how i).1 (norm_nonneg _) (how i).2.2
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj') m
  have hd : ‖D‖ ≤ 1 := by
    have h1 : (∑ i, o i * (j (s₀ (w i)) - j (w i))) ∈ ball ((l : Qbar l) ^ 0) := by
      refine sum_mem fun i _ => mul_mem_ball (how i).1 (sub_mem ?_ ?_)
      · simpa [mem_ball] using (hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 ((hj _).2 (how i).2.2))
      · simpa [mem_ball] using (how i).2.2
    have h2 := add_mem (ball_pow_mono hp1 (Nat.zero_le m) (mem_ball.2 (hyp s₀ hs₀ hm₀))) h1
    simpa [mem_ball, hu₀] using h2
  obtain ⟨t, rfl⟩ := exists_grp hj' hs₀ hm₀
  have key := hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a)
    (fun σ => lamv l m (res j σ.1)) m m le_rfl (fun σ => norm_lamv_le_one σ.2.2)
    (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀
    (fun k hk T X hT hX hh => hc' Ω A j hj' m k hk T X hT hX hh) D _ hd hx fun σ hσ => ?_
  · simpa [Cg, mem_ball] using key
  have hine : ∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ.1 x - x‖ < 1 := by
    intro x hx1
    obtain ⟨a, ha, hxa⟩ := exists_approx hj' 1 hx1
    have h1 : ‖x - j a‖ < 1 := lt_of_le_of_lt (mem_ball.1 hxa) (by simpa using hp1)
    have h2 : ‖j (res j σ.1 a - a)‖ < 1 :=
      (hj'.valuation_lt_one_iff _).1 (σ.2.1.2 a ((A.valuation_le_one_iff a).2 ha))
    have e : σ.1 x - x = σ.1 (x - j a) + (j (res j σ.1 a - a) + -(x - j a)) := by
      rw [map_sub, map_sub, res_spec]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (by rwa [norm_map_GK]) ?_)
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 (by rwa [norm_neg]))
  have hfix : ∀ i, σ.1 (o i) = o i := fun i => (how i).2.1 (σ.1.restrictScalars ℚ_[l]) hσ hine
  have e : σ • (∑ i, o i * j (w i)) - ∑ i, o i * j (w i) = ∑ i, o i * (j (res j σ.1 (w i)) - j (w i)) := by
    show σ.1 _ - _ = _
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hfix, res_spec]; ring
  rw [e]
  exact hyp _ σ.2.1 σ.2.2

theorem exists_kumVal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} {ζ u v : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hu : u ≠ 0) (hv : v ^ (l ^ m) = u) {s : G ℚ Ω} (hs : s u = u) :
    ∃ k : ZMod (l ^ m), s v = ζ ^ k.val * v := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have h1 : (s v / v) ^ (l ^ m) = 1 := by rw [div_pow, ← map_pow, hv, hs, div_self hu]
  obtain ⟨k, hk, e⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨(k : ZMod (l ^ m)), by rw [ZMod.val_cast_of_lt hk, e]; field_simp⟩

theorem kumVal_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {m c₀ : ℕ} (hc : c₀ ≤ m) {ζ u : Ω}
    (hζ : IsPrimitiveRoot (ζ ^ l ^ c₀) (l ^ (m - c₀))) (hu : u ≠ 0) {s : G ℚ Ω} (hs : s ζ = ζ) {k : ZMod (l ^ m)}
    {k' : ZMod (l ^ (m - c₀))} (hk : GlobalTheory.Col.KumVal m ζ u s k) (hk' : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s k') :
    (k'.val : Qbar l) - k.val ∈ ball ((l : Qbar l) ^ (m - c₀)) := by
  obtain ⟨v, hv, hsv⟩ := hk
  have h1 : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s ((k.val : ℕ) : ZMod (l ^ (m - c₀))) := by
    refine ⟨v ^ l ^ c₀, by rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hc, hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm k.val]
  have h2 := GlobalTheory.Col.kumVal_unique hζ (by rw [map_pow, hs]) hu hk' h1
  have h3 : (k.val : Qbar l) = k'.val + ((k.val / l ^ (m - c₀) : ℕ) : Qbar l) * (l : Qbar l) ^ (m - c₀) := by
    rw [h2, ZMod.val_natCast]
    exact_mod_cast congrArg (Nat.cast : ℕ → Qbar l) (Nat.mod_add_div' k.val (l ^ (m - c₀))).symm
  rw [h3, sub_add_cancel_left]
  exact neg_mem (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one _ _) (mem_ball.2 le_rfl))

theorem htv_coeff : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m c₀ Z ζ P o →
  ∀ y : (ZMod (l ^ m))ˣ, ∃ x : ι → Ω, (∀ i, x i ∈ A) ∧ ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) ((l : Qbar l) ^ c * Z m s y)
      ((l : Qbar l) ^ c * htv j ζ P o (y : ZMod (l ^ m)).val * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i))) := by
  intro l _ hl2
  obtain ⟨c, hc⟩ := GlobalTheory.RecConj.recip_conj l hl2
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A cf j hA hj ν Z m c₀ hm hν hZ ζ ι _ P o hP y
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  obtain ⟨hζ, hco, -, hP0, hζ0, -, hu, ho, hK⟩ := hP
  obtain ⟨⟨τ, hτ⟩, hτy⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A (valuation_lt_one hj') m y⁻¹
  have hτy' : cycMod ℚ Ω l m τ = y⁻¹ := hτy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ', hζ'⟩ := IsAlgClosed.exists_pow_nat_eq ζ hpos
  choose x hxA hgA hx using fun i => hc Ω A hA m ζ ζ' hζ hζ' (P i) (hco i) (hu i).1 (hu i).2.2 (hP0 i) τ y hτ hτy'
  refine ⟨x, hxA, fun s hs hs1 => ?_⟩
  have hs' : τ * s * τ⁻¹ ∈ Ine (F := ℚ) A := mul_mem (mul_mem hτ hs) (inv_mem hτ)
  have hs1' : cycMod ℚ Ω l m (τ * s * τ⁻¹) = 1 := by rw [map_mul, map_mul, hs1, map_inv, mul_one, mul_inv_cancel]
  have hfix : ∀ {g : G ℚ Ω}, cycMod ℚ Ω l m g = 1 → g ζ = ζ := fun hg => by
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
      haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
      inferInstance
    exact GlobalTheory.Col.fix_of_cycMod le_rfl hg hζ.pow_eq_one
  have hconj : Z m (τ * s * τ⁻¹) 1 = Z m s y := by
    have h1 := hZ τ (Ine_le_Dec A hτ) s (Ine_le_Dec A hs) 1
    have h2 := hZ _ (Ine_le_Dec A hs') τ (Ine_le_Dec A hτ) 1
    rw [hν τ hτ, hτy', inv_inv, one_mul, Units.val_one, one_mul] at h1
    rw [hν _ hs', hs1', inv_one, one_mul, Units.val_one, one_mul, inv_mul_cancel_right, h1, add_comm] at h2
    exact (add_right_cancel h2).symm
  obtain ⟨k', hk', hZk⟩ := hK _ hs' hs1' (by rw [map_pow, hfix hs1'])
  rw [hconj] at hZk
  have hPfix : ∀ i, (τ * s * τ⁻¹) ((P i).eval ζ) = (P i).eval ζ := by
    intro i
    rw [Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, hfix hs1']
    by_cases h : (P i).coeff n = 0
    · rw [h, map_zero]
    · rw [(hco i _ (Polynomial.coeff_mem_coeffs h)).2 _ hs']
  have hk : ∀ i, ∃ k : ZMod (l ^ m), GlobalTheory.Col.KumVal m ζ ((P i).eval ζ) (τ * s * τ⁻¹) k := by
    intro i
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((P i).eval ζ) hpos
    obtain ⟨k, hk⟩ := exists_kumVal hζ (hP0 i) hv (hPfix i)
    exact ⟨k, v, hv, hk⟩
  choose k hk using hk
  obtain ⟨t, ht⟩ := exists_kumVal hζ (hζ.ne_zero hpos.ne') hζ' (hfix hs1)
  have hlam : (t.val : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact sub_mem (by simpa [mem_ball] using IsUltrametricDist.norm_natCast_le_one (Qbar l) t.val)
        (by simpa [mem_ball] using norm_lamv_le_one hs1)
    · have hprim : IsPrimitiveRoot ζ' (l ^ (m + m)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have h1 : ¬ ζ' ^ l ^ (n + 1 + n) = 1 := by
          rw [pow_add l (n + 1) n, pow_mul, hζ']
          exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
            (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n))
        have h2 : ζ' ^ l ^ (n + 1 + n + 1) = 1 := by
          rw [add_assoc (n + 1), pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]
        have h3 := orderOf_eq_prime_pow h1 h2
        rw [show n + 1 + (n + 1) = n + 1 + n + 1 from rfl, ← h3]
        exact IsPrimitiveRoot.orderOf ζ'
      exact kummer_sub_lamv hprim hs1 (by rw [hζ']; exact ht)
  have hterm : ∀ i, (l : Qbar l) ^ c * (o i * ((k' i).val : Qbar l)) -
      ((l : Qbar l) ^ c * (o i * j (ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val))) * lamv l m s + o i * (j (s (x i)) - j (x i))) ∈
      ball ((l : Qbar l) ^ (m - c₀)) := by
    intro i
    have h1 := kumVal_sub_mem hm hζ0 (hP0 i) (hfix hs1') (hk i) (hk' i)
    have h2 := (cgA_iff hj' _ _ _).1 (hx i s hs hs1 _ t (hk i) ht)
    have h3 := (hj _).1 (hgA i)
    generalize ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val) = g at h2 h3 ⊢
    simp only [map_mul, map_add, map_sub, map_pow, map_natCast] at h2
    have h4 := mul_mem_ball (ho i) (add_mem (add_mem (mul_mem_ball hpc h1) (ball_pow_mono hp1 (Nat.sub_le m c₀) h2))
      (mul_mem_ball hpc (mul_mem_ball h3 (ball_pow_mono hp1 (Nat.sub_le m c₀) hlam))))
    convert h4 using 1
    ring
  have h5 := add_mem (mul_mem_ball hpc (mem_ball.2 hZk)) (sum_mem fun i (_ : i ∈ Finset.univ) => hterm i)
  refine mem_ball.1 ?_
  convert h5 using 1
  rw [htv, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem localGlue : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₁ : ℕ, ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ + c₁ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (h : (ZMod (l ^ m))ˣ → Qbar l),
    HTPresNuOfPolys A c m c₀ Z ζ P o → (∀ y, GlobalTheory.LambdaValuationPowers.HTCoL A c j Z m c₀ y (h y)) →
    ∀ y : (ZMod (l ^ m))ˣ, Cg (m - c₀ - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y) := by
  intro l _ hl Ω _ _ _ A c j hA hj
  obtain ⟨cA, hcA⟩ := htv_coeff l hl
  obtain ⟨c₂, hc₂⟩ := uniq_fix l hl Ω A c j hA hj
  refine ⟨cA + c₂, ?_⟩
  intro ν Z m c₀ hm hν hZ ζ ι _ P o h hP hh y
  obtain ⟨x, hxA, hx⟩ := hcA Ω A c j hA hj ν Z m c₀ (by omega) hν hZ ζ ι P o hP y
  obtain ⟨q, o', w', ho', hw'⟩ := hh y
  have hl0 : (l : Qbar l) ≠ 0 := GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hl1 : ‖(l : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hlpos : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 hl0
  set H := htv j ζ P o (y : ZMod (l ^ m)).val with hH
  let e := Fintype.equivFin ι
  let n := Fintype.card ι
  let o'' : Fin (q + n) → Qbar l :=
    Fin.append (fun i => (l : Qbar l) ^ cA * o' i) (fun i => -((l : Qbar l) ^ c₀ * o (e.symm i)))
  let w'' : Fin (q + n) → Ω := Fin.append w' (fun i => x (e.symm i))
  have hsum : ∀ s : G ℚ Ω, ∑ i, o'' i * (j (s (w'' i)) - j (w'' i)) =
      (l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
        (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i)) := by
    intro s
    rw [Fin.sum_univ_add]
    simp only [o'', w'', Fin.append_left, Fin.append_right]
    rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [← e.symm.sum_comp (fun i => -((l : Qbar l) ^ c₀ * (o i * (j (s (x i)) - j (x i)))))]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hoi : ∀ i, o i ∈ c.O := hP.2.2.1
  have hB : ∀ i, ‖o'' i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o'' i) ∧ ‖j (w'' i)‖ ≤ 1 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [o'', w'', Fin.append_left]
      obtain ⟨h1, h2, h3⟩ := ho' i
      refine ⟨?_, fun σ hσ hσ' => ?_, h3⟩
      · rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) h1
      · rw [map_mul, map_pow, map_natCast, h2 σ hσ hσ']
    · simp only [o'', w'', Fin.append_right]
      refine ⟨?_, fun σ hσ _ => ?_, (hj _).1 (hxA _)⟩
      · rw [norm_neg, norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hoi _))
      · rw [map_neg, map_mul, map_pow, map_natCast, hσ _ (hoi _)]
  have key := hc₂ m ((l : Qbar l) ^ (cA + c₀) * (H - h y)) (q + n) o'' w'' hB (by
    intro s hs hs1
    rw [hsum s]
    have h1 := hx s hs hs1
    have h2 := hw' s hs hs1
    unfold Cg at h1 h2 ⊢
    have e1 : (l : Qbar l) ^ (cA + c₀) * (H - h y) * GlobalTheory.LambdaValuationPowers.lamv l m s -
        ((l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
          (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i))) =
        (-(l : Qbar l) ^ c₀) * ((l : Qbar l) ^ cA * Z m s y -
          ((l : Qbar l) ^ cA * H * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i)))) +
        (l : Qbar l) ^ cA * ((l : Qbar l) ^ c₀ * Z m s y -
          ((l : Qbar l) ^ c₀ * h y * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o' i * (j (s (w' i)) - j (w' i)))) := by
      ring
    rw [e1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_neg, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ c₀ * ‖_‖ ≤ ‖(l : Qbar l)‖ ^ c₀ * ‖(l : Qbar l)‖ ^ (m - c₀) :=
            mul_le_mul_of_nonneg_left (by simpa [norm_pow] using h1) (by positivity)
        _ = ‖(l : Qbar l)‖ ^ m := by rw [← pow_add]; congr 1; omega
    · rw [norm_mul, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ cA * ‖_‖ ≤ 1 * ‖(l : Qbar l)‖ ^ m :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1.le) (by simpa [norm_pow] using h2) (norm_nonneg _) zero_le_one
        _ = ‖(l : Qbar l)‖ ^ m := one_mul _)
  unfold Cg at key ⊢
  rw [sub_zero, norm_mul, norm_pow, norm_pow] at key
  rw [norm_pow]
  have e2 : ‖(l : Qbar l)‖ ^ (m - c₂) = ‖(l : Qbar l)‖ ^ (cA + c₀) * ‖(l : Qbar l)‖ ^ (m - c₀ - (cA + c₂)) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at key
  exact le_of_mul_le_mul_left key (pow_pos hlpos _)

end GlobalTheory.LambdaValuationPowers.LocGlue
