import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.FiniteProjectionSingleSame
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.CellLocal

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

private theorem unit_or_unit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  have hu : IsUnit (a * d + (-(b * c))) := by
    rw [← sub_eq_add_neg, h]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h1 | h1
  · exact Or.inr (isUnit_of_mul_isUnit_right h1)
  · rw [IsUnit.neg_iff] at h1
    exact Or.inl (isUnit_of_mul_isUnit_right h1)

private theorem nat_isUnit {F : Type} [Field F] [NumberField F] (j : ℕ) (hj : 0 < j) :
    IsUnit ((j : ℕ) : A F) := by
  have h : ((j : ℕ) : A F) = algebraMap F (A F) (j : F) := (map_natCast _ j).symm
  rw [h]
  exact (IsUnit.mk0 (j : F) (Nat.cast_ne_zero.2 hj.ne')).map _

private theorem map_unit_or_unit {F : Type} [Field F] [NumberField F] {R : Type} [CommRing R]
    [IsLocalRing R] (f : A F →+* R) (g : G1 F) : IsUnit (f (g 1 0)) ∨ IsUnit (f (g 1 1)) := by
  refine unit_or_unit (a := f (g 0 0)) (b := f (g 0 1)) ?_
  rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]

private theorem inf_step {F : Type} [Field F] [NumberField F] (s : Finset (G1 F)) (w : InfinitePlace F) :
    ∃ n : ℕ, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * (n : w.Completion) ≠ 0 := by
  let f : A F →+* w.Completion :=
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).comp (p1 F)
  obtain ⟨n, hn⟩ := cellLocal w.Completion (G1 F) s (fun g => f (g 1 0)) (fun g => f (g 1 1))
    (fun j h0 _ => by simpa using (nat_isUnit (F := F) j h0).map f)
    (fun g _ => map_unit_or_unit f g)
  exact ⟨n, fun g hg => (hn g hg).ne_zero⟩

private theorem isUnit_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) : IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  exact Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

private theorem fin_step {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ n : ℕ, (∀ g ∈ s, pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F) ≠ 0) ∧
      ((∀ g ∈ s, IntAt v g) → (∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1) →
        ∀ g ∈ s, Valued.v (pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F)) = 1) := by
  by_cases hgood : (∀ g ∈ s, IntAt v g) ∧
      ∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1
  · obtain ⟨hint, hval⟩ := hgood
    let c : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 1 0), hint g.1 g.2 1 0⟩
    let d : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 1 1), hint g.1 g.2 1 1⟩
    let a : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 0 0), hint g.1 g.2 0 0⟩
    let b : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 0 1), hint g.1 g.2 0 1⟩
    obtain ⟨n, hn⟩ := cellLocal (v.adicCompletionIntegers F) {g // g ∈ s} s.attach c d
      (fun j h0 hj => by
        rw [isUnit_int_iff]
        simpa using hval j h0 (by simpa using hj))
      (fun g _ => by
        refine unit_or_unit (a := a g) (b := b g) (Subtype.ext ?_)
        have h := congrArg (pv v) (specialLinear_det_entries g.1)
        rw [map_sub, map_mul, map_mul, map_one] at h
        simpa [a, b, c, d] using h)
    have key : ∀ g ∈ s, Valued.v (pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F)) = 1 := by
      intro g hg
      have h := (isUnit_int_iff v _).1 (hn ⟨g, hg⟩ (Finset.mem_attach _ _))
      simpa [c, d] using h
    refine ⟨n, fun g hg h0 => ?_, fun _ _ => key⟩
    have h := key g hg
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · obtain ⟨n, hn⟩ := cellLocal (v.adicCompletion F) (G1 F) s (fun g => pv v (g 1 0)) (fun g => pv v (g 1 1))
      (fun j h0 _ => by simpa using (nat_isUnit (F := F) j h0).map (pv v))
      (fun g _ => map_unit_or_unit (pv v) g)
    exact ⟨n, fun g hg => (hn g hg).ne_zero, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩

private theorem eventually_good {F : Type} [Field F] [NumberField F] (s : Finset (G1 F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (∀ g ∈ s, IntAt v g) ∧
      ∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1 := by
  refine Filter.Eventually.and ((Filter.eventually_all_finset s).2 fun g _ => eventually_intAt g) ?_
  have h : ∀ j ∈ Finset.Icc 1 s.card, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Valued.v (j : v.adicCompletion F) = 1 := by
    intro j hj
    have hu := ((isUnit_adele_iff _).1 (nat_isUnit (F := F) j (Finset.mem_Icc.1 hj).1)).2.2
    filter_upwards [hu] with v hv
    have e : (((j : ℕ) : A F)).2 v = (j : v.adicCompletion F) := map_natCast (pv v) j
    rwa [e] at hv
  filter_upwards [(Filter.eventually_all_finset _).2 h] with v hv j h0 hj
  exact hv j (Finset.mem_Icc.2 ⟨h0, hj⟩)

theorem UpperTheory.ConvolutionTheory.R2.cellGeneric :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ x : A F, ∀ g ∈ s, g * nL x ∈ Cell F := by
  intro F _ _ s
  choose ni hi using inf_step s
  choose nf hf hf' using fin_step s
  let x : A F := (fun w => (ni w : w.Completion),
    ⟨fun v => (nf v : v.adicCompletion F), Filter.Eventually.of_forall fun v => natCast_mem _ _⟩)
  refine ⟨x, fun g hg => ?_⟩
  change IsUnit ((g * nL x) 1 0)
  have h00 : (nL x) 0 0 = 1 := rfl
  have h10 : (nL x) 1 0 = x := rfl
  rw [specialLinear_mul_entry, h00, h10, mul_one, isUnit_adele_iff]
  refine ⟨fun w => hi w g hg, fun v => hf v g hg, ?_⟩
  filter_upwards [eventually_good s] with v hv
  exact hf' v hv.1 hv.2 g hg
