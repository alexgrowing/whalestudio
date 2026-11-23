import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ResBig
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.UnitA

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma fieldCase (K : Type) [Field K] [CharZero K] {ι : Type} (s : Finset ι) (c d : ι → K)
    (h : ∀ i ∈ s, c i ≠ 0 ∨ d i ≠ 0) : ∃ t : K, ∀ i ∈ s, c i + d i * t ≠ 0 := by
  have hinf : Infinite (IsLocalRing.ResidueField K) :=
    Infinite.of_injective _ (IsLocalRing.residue K).injective
  have hc : ((s.image fun i => (c i, d i)).card : ℕ∞) < ENat.card (IsLocalRing.ResidueField K) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc K (s.image fun i => (c i, d i)) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    simpa [isUnit_iff_ne_zero] using h i hi) hc
  exact ⟨t, fun i hi => (ht _ (Finset.mem_image_of_mem _ hi)).ne_zero⟩

private lemma rowUnit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  by_contra hn
  push_neg at hn
  have hc : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).2 hn.1
  have hd : d ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal d).2 hn.2
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

private lemma row {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma valUnit {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) (h : IsUnit x) : Valued.v (x : v.adicCompletion F) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (u : v.adicCompletionIntegers F).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h3 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have h4 : (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
        (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      exact_mod_cast congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) u.mul_inv
    rw [h4, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

private lemma goodPlace {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F))
    (hint : ∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F)
    (hbig : (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    ∃ t : v.adicCompletion F, t ∈ v.adicCompletionIntegers F ∧
      ∀ g ∈ s, Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1 := by
  let toO : v.adicCompletion F → v.adicCompletionIntegers F :=
    fun x => if h : x ∈ v.adicCompletionIntegers F then ⟨x, h⟩ else 0
  have hto : ∀ x (h : x ∈ v.adicCompletionIntegers F), (toO x : v.adicCompletion F) = x := by
    intro x h
    simp only [toO, dif_pos h]
  let pr : G1 F → v.adicCompletionIntegers F × v.adicCompletionIntegers F :=
    fun g => (toO ((g 1 0).2 v), toO ((g 1 1).2 v))
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc (v.adicCompletionIntegers F) (s.image pr) (by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hp
    have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
      congrArg (fun x : A F => x.2 v) (row g)
    refine rowUnit (a := toO ((g 0 0).2 v)) (b := toO ((g 0 1).2 v)) (Subtype.ext ?_)
    push_cast
    rw [hto _ (hint g hg 0 0), hto _ (hint g hg 0 1), hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)]
    exact hdet) (lt_of_le_of_lt (by exact_mod_cast Finset.card_image_le) hbig)
  refine ⟨t, t.2, fun g hg => ?_⟩
  have h := valUnit v _ (ht _ (Finset.mem_image_of_mem pr hg))
  simp only [pr] at h
  push_cast at h
  rwa [hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)] at h

theorem UpperTheory.ConvolutionTheory.R2.C.generic :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0) := by
  intro F _ _ s
  have hI : ∀ w : InfinitePlace F, ∃ t : w.Completion, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * t ≠ 0 := by
    intro w
    haveI : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
    refine fieldCase w.Completion s (fun g => (g 1 0).1 w) (fun g => (g 1 1).1 w) fun g _ => ?_
    have hdet : (g 0 0).1 w * (g 1 1).1 w - (g 0 1).1 w * (g 1 0).1 w = 1 :=
      congrArg (fun x : A F => x.1 w) (row g)
    by_contra hn
    push_neg at hn
    simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  let G : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    (∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hG : ∀ᶠ v in cofinite, G v := by
    refine Filter.Eventually.and ?_ (UpperTheory.ConvolutionTheory.R2.C.resBig F s.card)
    refine (Filter.eventually_all_finset s).2 fun g _ => ?_
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact (g i j).2.2
  have hF : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F,
      (G v → t ∈ v.adicCompletionIntegers F) ∧
      ∀ g ∈ s, (g 1 0).2 v + (g 1 1).2 v * t ≠ 0 ∧
        (G v → Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1) := by
    intro v
    by_cases hv : G v
    · obtain ⟨t, ht, hu⟩ := goodPlace s v hv.1 hv.2
      refine ⟨t, fun _ => ht, fun g hg => ⟨fun h0 => ?_, fun _ => hu g hg⟩⟩
      have := hu g hg
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · obtain ⟨t, ht⟩ := fieldCase (v.adicCompletion F) s (fun g => (g 1 0).2 v)
        (fun g => (g 1 1).2 v) (fun g _ => by
          have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
            congrArg (fun x : A F => x.2 v) (row g)
          by_contra hn
          push_neg at hn
          simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
          exact zero_ne_one hdet)
      exact ⟨t, fun h => absurd h hv, fun g hg => ⟨ht g hg, fun h => absurd h hv⟩⟩
  choose tI htI using hI
  choose tF htF using hF
  let tf : FiniteAdeleRing (𝓞 F) F := ⟨tF, hG.mono fun v hv => (htF v).1 hv⟩
  let t : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F := (tI, tf)
  let t' : A F := t
  let u : G1 F := ⟨!![1, 0; t', 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨u, fun g hg => ?_⟩
  have hu : (g * u) 1 0 = g 1 0 + g 1 1 * t' := by
    show (g.1 * !![1, 0; t', 1]) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [hu]
  refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => htI w g hg, fun v => ((htF v).2 g hg).1, ?_⟩
  exact hG.mono fun v hv => ((htF v).2 g hg).2 hv
