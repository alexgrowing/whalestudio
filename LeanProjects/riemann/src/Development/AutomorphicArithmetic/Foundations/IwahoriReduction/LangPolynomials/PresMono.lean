import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem roots_pow {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : Roots l ζ) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]

private theorem nat_le_one {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

theorem pPresMono : SPresMono := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩
    infer_instance
  haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩
  refine ⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩
  obtain ⟨k, hk, hcg⟩ := h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hk i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]
  · have hz := hZ s ⟨hs, hc⟩
    unfold Cg at hz hcg ⊢
    have e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine hcg.trans ?_
      rw [pow_add, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact_mod_cast nat_le_one (l := l) (l ^ d)
    have e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1 := by
      refine Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)
    have e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) e2
    rw [norm_sub_rev] at hz
    have e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) =
        ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) +
        ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.val_natCast]
      conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]
      push_cast
      ring
    have := add_le (add_le hz e1) e3
    rw [e4] at this
    convert this using 2
    ring

end UpperTheory.Kd.C7
