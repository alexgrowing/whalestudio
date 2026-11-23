import Mathlib

open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi11.Af :
    (F : Type) → [inst : Field F] → [NumberField F] → Type :=
    fun (F : Type) [Field F] [NumberField F] ↦ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

theorem UpperTheory.Reformulated.B.Qi11.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v),
      ∀ᶠ (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
        Pi.single v a x ∈
          (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F x) :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F x)) := by
  intro F _ _ v a
  refine (Set.finite_singleton v).subset fun x hx => ?_
  by_contra h
  apply hx
  have hne : x ≠ v := h
  simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hne]
  exact zero_mem _

noncomputable def UpperTheory.Reformulated.B.Qi11.sglV :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
        (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ↦
      (⟨Pi.single v a, UpperTheory.Reformulated.B.Qi11.aux2 v a⟩ :
        { x :
          (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
              i //
          ∀ᶠ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
            x i ∈
              (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                  (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) :
                    Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)))
                i })

noncomputable def UpperTheory.Reformulated.B.Qi11.sglS :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F]
        (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
      ∑ v ∈ A, UpperTheory.Reformulated.B.Qi11.sglV v (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)

private theorem UpperTheory.Reformulated.B.Qi11.tendsto_cut {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)]
    [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} (h0 : ∀ i, (0 : R i) ∈ A i)
    (y z : RestrictedProduct R A Filter.cofinite) (hz : ∀ i, z i = 0)
    (f : Finset ι → RestrictedProduct R A Filter.cofinite)
    (hf : ∀ B i, f B i = if i ∈ B then 0 else y i) :
    Filter.Tendsto f Filter.atTop (nhds z) := by
  have hS : Filter.cofinite ≤ Filter.principal {i | y i ∈ A i} := Filter.le_principal_iff.2 y.2
  let g : Finset ι → RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := fun B =>
    ⟨fun i => if i ∈ B then 0 else y i, fun i hi => by
      show (if i ∈ B then 0 else y i) ∈ A i
      split_ifs
      · exact h0 i
      · exact hi⟩
  let o : RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := ⟨fun _ => 0, fun i _ => h0 i⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds o) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with B hB
    have hi : i ∈ B := hB (Finset.mem_singleton_self i)
    show (0 : R i) = if i ∈ B then 0 else y i
    rw [if_pos hi]
  have h1 : f = RestrictedProduct.inclusion R A hS ∘ g :=
    funext fun B => RestrictedProduct.ext _ _ fun i => hf B i
  have h2 : z = RestrictedProduct.inclusion R A hS o := RestrictedProduct.ext _ _ fun i => hz i
  rw [h1, h2]
  exact ((RestrictedProduct.continuous_inclusion hS).tendsto o).comp hg

private theorem UpperTheory.Reformulated.B.Qi11.sglS_apply {F : Type} [Field F] [NumberField F]
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Qi11.sglS A w = if w ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => rfl
  | insert v A hv ih =>
    have h : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) =
        UpperTheory.Reformulated.B.Qi11.sglV v 1 + UpperTheory.Reformulated.B.Qi11.sglS A := Finset.sum_insert hv
    have h' : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) w =
        (Pi.single v 1 : ∀ u, IsDedekindDomain.HeightOneSpectrum.adicCompletion F u) w +
          UpperTheory.Reformulated.B.Qi11.sglS A w := by
      rw [h]
      rfl
    rw [h', ih]
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]

theorem UpperTheory.Reformulated.B.Qi11.tendsto_fin :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : UpperTheory.Reformulated.B.Qi11.Af F),
      Filter.Tendsto
        (fun (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
          ((1 : UpperTheory.Reformulated.B.Qi11.Af F) - UpperTheory.Reformulated.B.Qi11.sglS A) * y)
        Filter.atTop (nhds (0 : UpperTheory.Reformulated.B.Qi11.Af F)) := by
  intro F _ _ y
  have key := UpperTheory.Reformulated.B.Qi11.tendsto_cut
    (R := fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
    (A := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      SetLike.coe (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
    (fun v => zero_mem _)
  refine key y (0 : UpperTheory.Reformulated.B.Qi11.Af F) (fun w => ?_)
    (fun B => ((1 - UpperTheory.Reformulated.B.Qi11.sglS B) * y : UpperTheory.Reformulated.B.Qi11.Af F)) fun B w => ?_
  · rfl
  · show (1 - UpperTheory.Reformulated.B.Qi11.sglS B w) * y w = if w ∈ B then 0 else y w
    rw [UpperTheory.Reformulated.B.Qi11.sglS_apply]
    split_ifs <;> simp
