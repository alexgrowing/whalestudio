import Mathlib

open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm :
    ∀ {X T : Type} [inst : Group X]
    [inst_1 : TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [inst_6 : MeasurableSpace X] [BorelSpace X] [inst_8 : Group T] [inst_9 : TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [inst_14 : MeasurableSpace T] [BorelSpace T]
    (μ : MeasureTheory.Measure X) [μ.IsHaarMeasure] (ν : MeasureTheory.Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X),
    Continuous (⇑i : T → X) →
      ∀ {a b Ψ : X → ENNReal},
        Measurable a →
          Measurable b →
            Measurable Ψ →
              (∀ (t : T) (x : X), Ψ ((i : T → X) t * x) = Ψ x) →
                (∀ (x : X), ∫⁻ (t : T), a ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                  (∀ (x : X), ∫⁻ (t : T), b ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                    ∫⁻ (x : X), Ψ x * a x ∂μ = ∫⁻ (x : X), Ψ x * b x ∂μ := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi a b Ψ ha hb hΨ hinv hA hB
  have him : Measurable (i : T → X) := hi.measurable
  have m1 : Measurable (fun p : X × T => i p.2 * p.1) :=
    (him.comp measurable_snd).mul measurable_fst
  have m2 : Measurable (fun p : X × T => i p.2⁻¹ * p.1) :=
    (him.comp measurable_snd.inv).mul measurable_fst
  have f1 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * a x * b (i t * x)) :=
    ((hΨ.comp measurable_fst).mul (ha.comp measurable_fst)).mul (hb.comp m1)
  have f2 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * b x * a (i t⁻¹ * x)) :=
    ((hΨ.comp measurable_fst).mul (hb.comp measurable_fst)).mul (ha.comp m2)
  have e1 : ∀ x : X, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν = Ψ x * a x := by
    intro x
    have hm : Measurable (fun t : T => b (i t * x)) := hb.comp (him.mul_const x)
    rw [lintegral_const_mul _ hm, hB x, mul_one]
  have e2 : ∀ x : X, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν = Ψ x * b x := by
    intro x
    have hm : Measurable (fun t : T => a (i t⁻¹ * x)) :=
      ha.comp ((him.comp measurable_inv).mul_const x)
    rw [lintegral_const_mul _ hm, lintegral_inv_eq_self (fun t : T => a (i t * x)), hA x, mul_one]
  have e3 : ∀ t : T, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ = ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => Ψ x * b x * a (i t⁻¹ * x)) (i t)]
    refine lintegral_congr fun x => ?_
    simp only [hinv, map_inv, inv_mul_cancel_left]
    ring
  calc ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν ∂μ :=
        lintegral_congr fun x => (e1 x).symm
    _ = ∫⁻ t, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ ∂ν := lintegral_lintegral_swap f1.aemeasurable
    _ = ∫⁻ t, ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ ∂ν := lintegral_congr e3
    _ = ∫⁻ x, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap f2.aemeasurable).symm
    _ = ∫⁻ x, Ψ x * b x ∂μ := lintegral_congr e2
