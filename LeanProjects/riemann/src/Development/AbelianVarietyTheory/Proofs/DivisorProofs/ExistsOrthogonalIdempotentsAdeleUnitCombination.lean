import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.PickUnit

variable {F : Type} [Field F] [NumberField F]

def compInf (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst _ _)

def compFin (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v).comp
    (RingHom.snd _ _)

theorem ext_comp {a b : AF F} (h1 : ∀ w, compInf w a = compInf w b) (h2 : ∀ v, compFin v a = compFin v b) :
    a = b :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem isUnit_of_comp {a : AF F} (h1 : ∀ w, compInf w a ≠ 0) (h2 : ∀ v, compFin v a ≠ 0)
    (h3 : ∀ᶠ v in Filter.cofinite, Valued.v (compFin v a) = 1) : IsUnit a :=
  Prod.isUnit_iff.2 ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (h1 w), FiniteAdeleRing.isUnit_iff.2 ⟨h2, h3⟩⟩

variable {ι : Type} [DecidableEq ι]

def ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) : AF F :=
  ((fun w => if a w = i then 1 else 0),
    ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : b v = i
      · simp only [h, if_true]; exact one_mem _
      · simp only [h, if_false]; exact zero_mem _⟩)

theorem compInf_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) (w : InfinitePlace F) :
    compInf w (ind a b i) = if a w = i then 1 else 0 := rfl

theorem compFin_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι)
    (v : HeightOneSpectrum (𝓞 F)) : compFin v (ind a b i) = if b v = i then 1 else 0 := rfl

end GlobalTheory.QSA.PickUnit

open GlobalTheory.QSA.PickUnit in

theorem GlobalTheory.QSA.exists_idem_pick_unit : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧
      (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  intro F _ _ ι _ n u hs
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
    refine ⟨fun _ => 0, fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact isUnit_zero_iff.1 hs
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact hs
  have hinf : ∀ w, ∃ i, compInf w (n i) ≠ 0 := by
    intro w
    by_contra h
    push_neg at h
    apply (hs.map (compInf w)).ne_zero
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h i, mul_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, ∀ j, Valued.v (compFin v (n j)) ≤ Valued.v (compFin v (n i)) := by
    intro v
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => Valued.v (compFin v (n j)))
      ⟨i₀, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose a ha using hinf
  choose b hb using hfin
  refine ⟨ind a b, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ext_comp
    · intro w; rw [map_mul, compInf_ind]; split_ifs <;> simp
    · intro v; rw [map_mul, compFin_ind]; split_ifs <;> simp
  · intro i j hij
    apply ext_comp
    · intro w; rw [map_mul, map_zero, compInf_ind, compInf_ind]
      by_cases h1 : a w = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro v; rw [map_mul, map_zero, compFin_ind, compFin_ind]
      by_cases h1 : b v = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
  · apply ext_comp
    · intro w; rw [map_sum, map_one]; simp only [compInf_ind]; rw [Finset.sum_ite_eq]; simp
    · intro v; rw [map_sum, map_one]; simp only [compFin_ind]; rw [Finset.sum_ite_eq]; simp
  · have hcInf : ∀ w, compInf w (∑ i, ind a b i * n i) = compInf w (n (a w)) := by
      intro w
      rw [map_sum, Finset.sum_eq_single (a w)]
      · rw [map_mul, compInf_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compInf_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcFin : ∀ v, compFin v (∑ i, ind a b i * n i) = compFin v (n (b v)) := by
      intro v
      rw [map_sum, Finset.sum_eq_single (b v)]
      · rw [map_mul, compFin_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compFin_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    apply isUnit_of_comp
    · intro w; rw [hcInf]; exact ha w
    · intro v h0
      rw [hcFin] at h0
      apply (hs.map (compFin v)).ne_zero
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h := hb v j
      rw [h0, map_zero] at h
      rw [map_mul, (Valuation.zero_iff _).1 (le_antisymm h zero_le'), mul_zero]
    · have hsu := (FiniteAdeleRing.isUnit_iff.1 (hs.map (RingHom.snd (InfiniteAdeleRing F) (Af F)))).2
      have hint : ∀ᶠ v in Filter.cofinite, ∀ j,
          Valued.v (compFin v (u j)) ≤ 1 ∧ Valued.v (compFin v (n j)) ≤ 1 := by
        refine Filter.eventually_all.2 fun j => ?_
        filter_upwards [(u j).2.2, (n j).2.2] with v h1 h2
        exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h1,
          (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h2⟩
      filter_upwards [hsu, hint] with v hv1 hv2
      rw [hcFin]
      refine le_antisymm (hv2 _).2 ?_
      have hv1' : Valued.v (compFin v (∑ i, u i * n i)) = 1 := hv1
      rw [← hv1', map_sum]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le' (hv2 j).1).trans (hb v j)
