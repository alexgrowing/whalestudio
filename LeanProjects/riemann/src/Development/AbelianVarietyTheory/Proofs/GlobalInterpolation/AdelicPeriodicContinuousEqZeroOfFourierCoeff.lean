import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacterStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOneStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal ComplexConjugate Pointwise

namespace GlobalTheory.SWQ.FZero

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev Lat (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

abbrev Q (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) ⧸ Lat F N

theorem rat_neg (ξ : Fin N → F) : rat (-ξ) = -rat ξ := by
  funext l; simp [rat]

theorem Bd_add_left (a : Fin N → F) (u u' w : Fin N → AF F) :
    Bd (AF F) a (u + u') w = Bd (AF F) a u w + Bd (AF F) a u' w := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext l; ring

theorem Bd_rat_add (a : Fin N → F) (u : Fin N → AF F) (ξ η : Fin N → F) :
    Bd (AF F) a u (rat (ξ + η)) = Bd (AF F) a u (rat ξ) + Bd (AF F) a u (rat η) := by
  simp only [Bd, rat, Pi.add_apply, map_add, ← Finset.sum_add_distrib]; congr 1; funext l; ring

theorem Bd_rat_zero (a : Fin N → F) (u : Fin N → AF F) : Bd (AF F) a u (rat 0) = 0 := by
  simp [Bd, rat]

theorem Bd_rat_neg (a : Fin N → F) (u : Fin N → AF F) (ξ : Fin N → F) :
    Bd (AF F) a u (rat (-ξ)) = -Bd (AF F) a u (rat ξ) := by
  have h := Bd_rat_add a u ξ (-ξ)
  rw [add_neg_cancel, Bd_rat_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem Bd_rat_rat (a : Fin N → F) (η ξ : Fin N → F) :
    Bd (AF F) a (rat η) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) := by
  simp [Bd, rat, map_sum, map_mul]

theorem cont_Bd (a : Fin N → F) (w : Fin N → AF F) : Continuous fun u : Fin N → AF F => Bd (AF F) a u w := by
  unfold Bd
  exact continuous_finset_sum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

def chi (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (ξ : Fin N → F) (u : Fin N → AF F) : ℂ :=
  ψ (-(Bd (AF F) a u (rat ξ)))

variable {ψ : AddChar (AF F) ℂ} {a : Fin N → F}

theorem psi_conj (hψ : IsCharAF F ψ) (x : AF F) : conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.2.1 x]; simp

theorem chi_periodic (hψ : IsCharAF F ψ) (ξ η : Fin N → F) (u : Fin N → AF F) :
    chi ψ a ξ (rat η + u) = chi ψ a ξ u := by
  rw [chi, chi, Bd_add_left, Bd_rat_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]

theorem periodic_of (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) {f : (Fin N → AF F) → ℂ}
    (hf : ∀ ξ u, f (rat ξ + u) = f u) : ∀ g ∈ Lat F N, ∀ u, f (g + u) = f u := by
  intro g hg u
  obtain ⟨ξ, rfl⟩ := (hL g).1 hg
  exact hf ξ u

def liftQ (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) (f : (Fin N → AF F) → ℂ)
    (hf : ∀ ξ u, f (rat ξ + u) = f u) : Q F N → ℂ :=
  Quotient.lift f (by
    intro x y hxy
    have h : -x + y ∈ Lat F N := QuotientAddGroup.leftRel_apply.1 hxy
    have := periodic_of hL hf (-x + y) h x
    rw [show -x + y + x = y by abel] at this
    exact this.symm)

def liftC (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) (f : (Fin N → AF F) → ℂ)
    (hf : ∀ ξ u, f (rat ξ + u) = f u) (hc : Continuous f) : C(Q F N, ℂ) :=
  ⟨liftQ hL f hf, hc.quotient_lift _⟩

theorem liftC_apply (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) (f : (Fin N → AF F) → ℂ)
    (hf : ∀ ξ u, f (rat ξ + u) = f u) (hc : Continuous f) (u : Fin N → AF F) :
    liftC hL f hf hc (u : Q F N) = f u := rfl

def chiC (a : Fin N → F) (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) (hψ : IsCharAF F ψ) (ξ : Fin N → F) : C(Q F N, ℂ) :=
  liftC hL (chi ψ a ξ) (fun η u => chi_periodic hψ ξ η u) (hψ.1.comp (cont_Bd a _).neg)

variable (a) (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ) (hψ : IsCharAF F ψ)

theorem chiC_apply (ξ : Fin N → F) (u : Fin N → AF F) :
    chiC a hL hψ ξ (u : Q F N) = ψ (-(Bd (AF F) a u (rat ξ))) := rfl

theorem chiC_mul (ξ η : Fin N → F) :
    chiC a hL hψ ξ * chiC a hL hψ η = chiC a hL hψ (ξ + η) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, Bd_rat_add, neg_add, AddChar.map_add_eq_mul]

theorem chiC_zero : chiC a hL hψ 0 = 1 := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, Bd_rat_zero, neg_zero, AddChar.map_zero_eq_one]

theorem chiC_star (ξ : Fin N → F) : star (chiC a hL hψ ξ) = chiC a hL hψ (-ξ) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply, Bd_rat_neg]
  exact psi_conj hψ _

def Achar : StarSubalgebra ℂ C(Q F N, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC a hL hψ))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨ξ, rfl⟩ := hx
        obtain ⟨η, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨ξ + η, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero a hL hψ]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero a hL hψ]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ξ, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-ξ, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h

end GlobalTheory.SWQ.FZero

namespace GlobalTheory.SWQ.FZero

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem bdd_of_periodic {K : Set (Fin N → AF F)} (hK : IsCompact K) (hKc : ∀ u, ∃ ξ, u - rat ξ ∈ K)
    (g : (Fin N → AF F) → ℂ) (hg : Continuous g) (hp : ∀ ξ u, g (rat ξ + u) = g u) :
    ∃ C, ∀ u, ‖g u‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨ξ, hξ⟩ := hKc u
  have e : g (u - rat ξ) = g u := by
    rw [show u - rat ξ = rat (-ξ) + u by rw [rat_neg]; abel, hp]
  rw [← e]
  exact hC _ hξ

theorem integrableOn_of_bdd {g : (Fin N → AF F) → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ u, ‖g u‖ ≤ C)
    (μ : Measure (Fin N → AF F)) (D : Set (Fin N → AF F)) (hD : μ D ≠ ∞) : IntegrableOn g D μ :=
  Measure.integrableOn_of_bounded hD hg.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hC)

theorem mem_of_chi {ψ : AddChar (AF F) ℂ} {a : Fin N → F}
    (hann : ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ)
    (ha : ∀ l, a l ≠ 0) (y : Fin N → AF F) (hy : ∀ ξ, ψ (-(Bd (AF F) a y (rat ξ))) = 1) : y ∈ Lat F N := by
  have hl : ∀ l, ∃ c : F, y l = algebraMap F (AF F) c := by
    intro l
    apply hann
    intro ζ
    have h2 : (2 * a l) ≠ 0 := mul_ne_zero two_ne_zero (ha l)
    have e : Bd (AF F) a y (rat (Pi.single l (-(ζ / (2 * a l))))) = -(y l * algebraMap F (AF F) ζ) := by
      rw [Bd, Finset.sum_eq_single l]
      · simp only [rat, Pi.single_eq_same]
        have hal := ha l
        have h3 : (2 * a l) * (-(ζ / (2 * a l))) = -ζ := by field_simp
        calc algebraMap F (AF F) (2 * a l) * y l * algebraMap F (AF F) (-(ζ / (2 * a l)))
            = y l * algebraMap F (AF F) ((2 * a l) * (-(ζ / (2 * a l)))) := by
              rw [map_mul (algebraMap F (AF F)) (2 * a l) (-(ζ / (2 * a l))), mul_comm (algebraMap F (AF F) (2 * a l)) (y l), mul_assoc]
          _ = _ := by rw [h3, map_neg, mul_neg]
      · intro m _ hm; simp [rat, Pi.single_eq_of_ne hm]
      · intro h; exact absurd (Finset.mem_univ l) h
    have := hy (Pi.single l (-(ζ / (2 * a l))))
    rwa [e, neg_neg] at this
  choose c hc using hl
  exact AddSubgroup.subset_closure ⟨c, funext fun l => (hc l).symm⟩

theorem compact_Q {K : Set (Fin N → AF F)} (hK : IsCompact K) (hKc : ∀ u, ∃ ξ, u - rat ξ ∈ K) :
    CompactSpace (Q F N) := by
  refine ⟨?_⟩
  have h : (Set.univ : Set (Q F N)) = (QuotientAddGroup.mk : (Fin N → AF F) → Q F N) '' K := by
    ext q
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨ξ, hξ⟩ := hKc z
    refine ⟨z - rat ξ, hξ, ?_⟩
    rw [QuotientAddGroup.eq, show -(z - rat ξ) + z = rat ξ by abel]
    exact AddSubgroup.subset_closure ⟨ξ, rfl⟩
  rw [h]
  exact hK.image continuous_quotient_mk'

end GlobalTheory.SWQ.FZero

namespace GlobalTheory.SWQ.FZero

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eq_zero_of (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (hψ : IsCharAF F ψ)
    (hann : ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ)
    (ha : ∀ l, a l ≠ 0) (hL : ∀ u, u ∈ Lat F N ↔ ∃ ξ, u = rat ξ)
    {K : Set (Fin N → AF F)} (hK : IsCompact K) (hKc : ∀ u, ∃ ξ, u - rat ξ ∈ K)
    (μ : Measure (Fin N → AF F)) (hμ : μ.IsAddHaarMeasure) (D : Set (Fin N → AF F))
    (hD : IsAddFundamentalDomain (Lat F N) D μ) (hDf : μ D ≠ ∞)
    (P : (Fin N → AF F) → ℂ) (hPc : Continuous P) (hPp : ∀ ξ u, P (rat ξ + u) = P u)
    (hcoef : ∀ ξ : Fin N → F, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂μ = 0) : P = 0 := by
  have := compact_Q hK hKc
  obtain ⟨C, hC⟩ := bdd_of_periodic hK hKc P hPc hPp
  have hint : ∀ g : C(Q F N, ℂ), IntegrableOn (fun u => P u * g (u : Q F N)) D μ := by
    intro g
    obtain ⟨C', hC'⟩ := bdd_of_periodic hK hKc (fun u => P u * g (u : Q F N))
      (hPc.mul (g.continuous.comp continuous_quotient_mk')) (fun ξ u => by
        rw [hPp]
        congr 2
        rw [QuotientAddGroup.eq, show -(rat ξ + u) + u = -rat ξ by abel]
        exact neg_mem (AddSubgroup.subset_closure ⟨ξ, rfl⟩))
    exact integrableOn_of_bdd (hPc.mul (g.continuous.comp continuous_quotient_mk')) hC' μ D hDf

  have hvan : ∀ g ∈ Achar a hL hψ, ∫ u in D, P u * g (u : Q F N) ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ξ, rfl⟩ := hx
      exact hcoef ξ
    | zero => simp
    | add x y hx hy h1 h2 =>
      simp only [ContinuousMap.add_apply, mul_add]
      rw [integral_add (hint x) (hint y), h1, h2, add_zero]
    | smul c x hx h =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      have e : (fun u : Fin N → AF F => P u * (c * x (u : Q F N))) = fun u => c * (P u * x (u : Q F N)) := by
        funext u; ring
      rw [e, integral_const_mul, h, mul_zero]

  have hsep : (Achar a hL hψ).SeparatesPoints := by
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective q'
    have hnot : x - x' ∉ Lat F N := by
      intro h
      apply hqq'
      rw [QuotientAddGroup.eq, show -x + x' = -(x - x') by abel]
      exact neg_mem h
    obtain ⟨ξ, hξ⟩ : ∃ ξ, ψ (-(Bd (AF F) a (x - x') (rat ξ))) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hnot (mem_of_chi hann ha _ h)
    refine ⟨chiC a hL hψ ξ, ⟨chiC a hL hψ ξ, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩, ?_⟩
    intro heq
    apply hξ
    have e1 : Bd (AF F) a x (rat ξ) = Bd (AF F) a (x - x') (rat ξ) + Bd (AF F) a x' (rat ξ) := by
      rw [← Bd_add_left, sub_add_cancel]
    have h1 : chiC a hL hψ ξ (x : Q F N) = chiC a hL hψ ξ (x' : Q F N) := heq
    rw [chiC_apply, chiC_apply, e1, neg_add, AddChar.map_add_eq_mul] at h1
    have hne : ψ (-(Bd (AF F) a x' (rat ξ))) ≠ 0 := by
      intro h0; have := hψ.2.1 (-(Bd (AF F) a x' (rat ξ))); rw [h0, norm_zero] at this; exact zero_ne_one this
    calc ψ (-(Bd (AF F) a (x - x') (rat ξ)))
        = ψ (-(Bd (AF F) a (x - x') (rat ξ))) * ψ (-(Bd (AF F) a x' (rat ξ))) /
            ψ (-(Bd (AF F) a x' (rat ξ))) := by field_simp
      _ = 1 := by rw [h1, div_self hne]
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (Achar a hL hψ) hsep
  have hcp : ∀ ξ u, conj (P (rat ξ + u)) = conj (P u) := fun ξ u => by rw [hPp]
  let Pb : C(Q F N, ℂ) := liftC hL (fun u => conj (P u)) hcp (Complex.continuous_conj.comp hPc)
  have hmem : Pb ∈ closure ((Achar a hL hψ : Set C(Q F N, ℂ))) := by
    have : Pb ∈ (Achar a hL hψ).topologicalClosure := by rw [hclos]; exact StarSubalgebra.mem_top
    exact this
  have hint0 : ∫ u in D, P u * conj (P u) ∂μ = 0 := by
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    set M := μ.real D
    have hM : 0 ≤ M := measureReal_nonneg
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem (ε / ((C + 1) * (M + 1)))
      (by positivity)
    have e : ∫ u in D, P u * conj (P u) ∂μ = ∫ u in D, P u * (Pb - b) (u : Q F N) ∂μ := by
      have h1 := hvan b hb
      have h2 : ∫ u in D, P u * (Pb - b) (u : Q F N) ∂μ =
          ∫ u in D, P u * Pb (u : Q F N) ∂μ - ∫ u in D, P u * b (u : Q F N) ∂μ := by
        simp only [ContinuousMap.sub_apply, mul_sub]
        exact integral_sub (hint Pb) (hint b)
      rw [h2, h1, sub_zero]
      rfl
    rw [e, zero_add]
    have hbd : ∀ u ∈ D, ‖P u * (Pb - b) (u : Q F N)‖ ≤ C * (ε / ((C + 1) * (M + 1))) := by
      intro u _
      rw [norm_mul]
      refine mul_le_mul (hC u) ?_ (norm_nonneg _) hC0
      refine le_trans (ContinuousMap.norm_coe_le_norm _ _) ?_
      rw [← dist_eq_norm]; exact hdist.le
    calc ‖∫ u in D, P u * (Pb - b) (u : Q F N) ∂μ‖
        ≤ C * (ε / ((C + 1) * (M + 1))) * M := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hDf) hbd
      _ ≤ ε := by
          rw [show C * (ε / ((C + 1) * (M + 1))) * M = ε * (C / (C + 1)) * (M / (M + 1)) by
            field_simp]
          have h1 : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have h2 : M / (M + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have h3 : 0 ≤ C / (C + 1) := by positivity
          have h4 : 0 ≤ M / (M + 1) := by positivity
          nlinarith [mul_le_mul h1 h2 h4 zero_le_one]
  have hsq : ∫ u in D, ‖P u‖ ^ 2 ∂μ = 0 := by
    have e : (fun u => P u * conj (P u)) = fun u => ((‖P u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e, integral_complex_ofReal] at hint0
    exact_mod_cast hint0
  have hInt : IntegrableOn (fun u => ‖P u‖ ^ 2) D μ := by
    haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hDf
    refine Integrable.mono' (integrable_const (C ^ 2)) (hPc.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC u) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => by positivity) hInt).1 hsq

  set t : Set (Fin N → AF F) := {u | P u ≠ 0} with ht
  have hto : IsOpen t := isOpen_ne_fun hPc continuous_const
  have htD : μ (t ∩ D) = 0 := by
    have h1 : (μ.restrict D) t = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      refine measure_mono_null (fun u hu => ?_) hae
      simp only [Set.mem_setOf_eq, Pi.zero_apply]
      intro h0
      exact hu (by simpa using h0)
    rwa [Measure.restrict_apply hto.measurableSet] at h1
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hcount : Countable (Lat F N) := by
    have hs : ((Lat F N : Set (Fin N → AF F))).Countable := by
      have : (Lat F N : Set (Fin N → AF F)) = Set.range (rat : (Fin N → F) → (Fin N → AF F)) := by
        ext u; simp only [SetLike.mem_coe, hL, Set.mem_range]
        exact ⟨fun ⟨ξ, h⟩ => ⟨ξ, h.symm⟩, fun ⟨ξ, h⟩ => ⟨ξ, h.symm⟩⟩
      rw [this]; exact Set.countable_range _
    exact hs.to_subtype
  have : MeasurableConstVAdd (Lat F N) (Fin N → AF F) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (Lat F N) (Fin N → AF F) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : Fin N → AF F) s⟩
  have hinv : ∀ g : Lat F N, g +ᵥ t = t := by
    intro g
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [ht, Set.mem_setOf_eq]
    have := periodic_of hL hPp (-(g : Fin N → AF F)) (neg_mem g.2) u
    show P (-(g : Fin N → AF F) + u) ≠ 0 ↔ P u ≠ 0
    rw [this]
  have ht0 : μ t = 0 := hD.measure_zero_of_invariant t hinv htD
  have hte : t = ∅ := by
    by_contra hne
    exact (hto.measure_pos μ (Set.nonempty_iff_ne_empty.2 hne)).ne' ht0
  funext u
  by_contra hu
  have : u ∈ t := hu
  rw [hte] at this
  exact this

end GlobalTheory.SWQ.FZero

namespace GlobalTheory.SWQ

theorem periodic_eq_zero_of_coeff : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) →
      (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ P : (Fin N → AF F) → ℂ, Continuous P →
    (∀ ξ u, P (rat ξ + u) = P u) →
    (∀ ξ : Fin N → F, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0) → P = 0 := by
  intro F _ _ N ψ lam ν a hctx D hD hD1 P hPc hPp hcoef
  obtain ⟨hTR, hψ, -, hcov, ha⟩ := hctx
  obtain ⟨hμ, hL, -, ⟨K, hK, hKc⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hcov
  exact FZero.eq_zero_of ψ a hψ (GlobalTheory.T.numberField_self_annihilator_adeleCharacter F hTR ψ hψ).2 ha hL hK hKc (muV N ν) hμ D hD
    (by rw [hD1]; exact ENNReal.one_ne_top) P hPc hPp hcoef

end GlobalTheory.SWQ
