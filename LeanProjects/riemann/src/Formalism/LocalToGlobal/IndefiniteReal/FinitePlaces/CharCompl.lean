import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate Pointwise

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

abbrev QO : Type := MO S T ⧸ ratL T S

def chiO (ψ : AddChar (AF D.host.F) ℂ) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) : ℂ :=
  ψ (symplO S T z (ratW T S a))

theorem periodic_of {f : MO S T → ℂ} (hf : ∀ a z, f (ratW T S a + z) = f z) :
    ∀ g ∈ ratL T S, ∀ z, f (g + z) = f z := by
  intro g hg z
  obtain ⟨a, rfl⟩ := (mem_ratL_iff S T g).1 hg
  exact hf a z

theorem chiO_periodic (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    chiO S T ψ a (ratW T S b + z) = chiO S T ψ a z := by
  unfold chiO
  rw [symplO_add_left, AddChar.map_add_eq_mul, psi_rat hψ, one_mul]

def liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) : QO S T → ℂ :=
  Quotient.lift f (by
    intro x y hxy
    have h : -x + y ∈ ratL T S := QuotientAddGroup.leftRel_apply.1 hxy
    have := periodic_of S T hf (-x + y) h x
    rw [show -x + y + x = y by abel] at this
    exact this.symm)

theorem cont_liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) :
    Continuous (liftQ S T f hf) :=
  hc.quotient_lift _

def liftC (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) : C(QO S T, ℂ) :=
  ⟨liftQ S T f hf, cont_liftQ S T f hf hc⟩

theorem compact_QO : CompactSpace (QO S T) := by
  obtain ⟨K, hK, hsub⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  refine ⟨?_⟩
  have h : (Set.univ : Set (QO S T)) = (QuotientAddGroup.mk : MO S T → QO S T) '' K := by
    ext q
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨a, ha⟩ := exists_rat_shift S T z
    refine ⟨ratW T S a + z, hsub ha, ?_⟩
    rw [QuotientAddGroup.eq]
    rw [show -(ratW T S a + z) + z = ratW T S (-a) by rw [ratW_neg]; abel]
    exact ⟨-a, rfl⟩
  rw [h]
  exact hK.image continuous_quotient_mk'

def chiC (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : C(QO S T, ℂ) :=
  liftC S T (chiO S T ψ a) (fun b z => chiO_periodic S T hψ a b z)
    ((psi_cont hψ).comp (cont_symplO_left S T _))

theorem chiC_apply (hψ : IsStdChar D ψ (-1)) (a) (z : MO S T) :
    chiC S T hψ a (z : QO S T) = ψ (symplO S T z (ratW T S a)) := rfl

theorem chiC_mul (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    chiC S T hψ a * chiC S T hψ b = chiC S T hψ (a + b) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, ratW_add, symplO_add_right, AddChar.map_add_eq_mul]

theorem chiC_zero (hψ : IsStdChar D ψ (-1)) : chiC S T hψ 0 = 1 := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, ratW_zero, symplO_zero_right, AddChar.map_zero_eq_one]

theorem chiC_star (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    star (chiC S T hψ a) = chiC S T hψ (-a) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply, ratW_neg, symplO_neg_right]
  exact psi_conj hψ _

def Achar (hψ : IsStdChar D ψ (-1)) : StarSubalgebra ℂ C(QO S T, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC S T hψ))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨a + b, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero S T hψ]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero S T hψ]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h

theorem comp_mk_periodic (g : C(QO S T, ℂ)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    g ((ratW T S a + z : MO S T) : QO S T) = g (z : QO S T) := by
  congr 1
  rw [QuotientAddGroup.eq, show -(ratW T S a + z) + z = ratW T S (-a) by rw [ratW_neg]; abel]
  exact ⟨-a, rfl⟩

theorem cont_comp_mk (g : C(QO S T, ℂ)) : Continuous fun z : MO S T => g (z : QO S T) :=
  g.continuous.comp continuous_quotient_mk'

theorem integrableOn_mul_comp (hψ : IsStdChar D ψ (-1)) {φ : MO S T → ℂ} (hφc : Continuous φ)
    (hφp : ∀ a z, φ (ratW T S a + z) = φ z) (g : C(QO S T, ℂ)) (μ : Measure (MO S T)) (𝓕 : Set (MO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) :
    IntegrableOn (fun z => φ z * g (z : QO S T)) 𝓕 μ :=
  integrableOn_of_periodic S T _ (hφc.mul (cont_comp_mk S T g))
    (fun a z => by simp only [Pi.mul_apply]; rw [hφp, comp_mk_periodic]) μ 𝓕 hμ h𝓕

theorem charCompleteB_of (hψ : IsStdChar D ψ (-1))
    (ha : ∀ x : MO S T, (∀ γ, ψ (symplO S T x (ratW T S γ)) = 1) → x ∈ ratL T S)
    (μ : Measure (MO S T)) (𝓕 : Set (MO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (φ : MO S T → ℂ) (hφc : Continuous φ)
    (hφp : ∀ γ w, φ (ratW T S γ + w) = φ w)
    (hcoef : ∀ γ, ∫ w in 𝓕, φ w * ψ (symplO S T w (ratW T S γ)) ∂μ = 0) : φ = 0 := by
  have := compact_QO S T

  have hvan : ∀ g ∈ Achar S T hψ, ∫ z in 𝓕, φ z * g (z : QO S T) ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hcoef a
    | zero => simp
    | add x y hx hy h1 h2 =>
      simp only [ContinuousMap.add_apply, mul_add]
      rw [integral_add (integrableOn_mul_comp S T hψ hφc hφp x μ 𝓕 hμ h𝓕)
        (integrableOn_mul_comp S T hψ hφc hφp y μ 𝓕 hμ h𝓕), h1, h2, add_zero]
    | smul c x hx h =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      have e : (fun z : MO S T => φ z * (c * x (z : QO S T))) = fun z => c * (φ z * x (z : QO S T)) := by
        funext z; ring
      rw [e, integral_const_mul, h, mul_zero]

  have hsep : (Achar S T hψ).SeparatesPoints := by
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective q'
    have hnot : x - x' ∉ ratL T S := by
      intro h
      apply hqq'
      rw [QuotientAddGroup.eq]
      have : -x + x' = -(x - x') := by abel
      rw [this]; exact neg_mem h
    obtain ⟨γ, hγ⟩ : ∃ γ, ψ (symplO S T (x - x') (ratW T S γ)) ≠ 1 := by
      by_contra h
      push Not at h
      exact hnot (ha _ h)
    refine ⟨chiC S T hψ γ, ⟨chiC S T hψ γ, Submodule.subset_span ⟨γ, rfl⟩, rfl⟩, ?_⟩
    intro heq
    apply hγ
    have e1 : symplO S T x (ratW T S γ) = symplO S T (x - x') (ratW T S γ) + symplO S T x' (ratW T S γ) := by
      rw [← symplO_add_left, sub_add_cancel]
    have h1 : chiC S T hψ γ (x : QO S T) = chiC S T hψ γ (x' : QO S T) := heq
    rw [chiC_apply, chiC_apply, e1, AddChar.map_add_eq_mul] at h1
    have hne := psi_ne hψ (symplO S T x' (ratW T S γ))
    calc ψ (symplO S T (x - x') (ratW T S γ))
        = ψ (symplO S T (x - x') (ratW T S γ)) * ψ (symplO S T x' (ratW T S γ)) /
            ψ (symplO S T x' (ratW T S γ)) := by field_simp
      _ = 1 := by rw [h1, div_self hne]
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (Achar S T hψ) hsep

  have hcp : ∀ a z, conj (φ (ratW T S a + z)) = conj (φ z) := fun a z => by rw [hφp]
  let φb : C(QO S T, ℂ) := liftC S T (fun z => conj (φ z)) hcp (Complex.continuous_conj.comp hφc)
  have hmem : φb ∈ closure ((Achar S T hψ : Set C(QO S T, ℂ))) := by
    have : φb ∈ (Achar S T hψ).topologicalClosure := by rw [hclos]; exact StarSubalgebra.mem_top
    exact this

  obtain ⟨C, hC⟩ := bdd_of_periodic S T φ hφc (fun a z => by rw [hφp])
  have hfin := measure_FD_lt_top S T μ 𝓕 hμ h𝓕
  have hint0 : ∫ z in 𝓕, φ z * conj (φ z) ∂μ = 0 := by
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    set M := μ.real 𝓕
    have hM : 0 ≤ M := measureReal_nonneg
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem (ε / ((C + 1) * (M + 1)))
      (by positivity)
    have e : ∫ z in 𝓕, φ z * conj (φ z) ∂μ = ∫ z in 𝓕, φ z * (φb - b) (z : QO S T) ∂μ := by
      have h1 := hvan b hb
      have h2 : ∫ z in 𝓕, φ z * (φb - b) (z : QO S T) ∂μ =
          ∫ z in 𝓕, φ z * φb (z : QO S T) ∂μ - ∫ z in 𝓕, φ z * b (z : QO S T) ∂μ := by
        simp only [ContinuousMap.sub_apply, mul_sub]
        exact integral_sub (integrableOn_mul_comp S T hψ hφc hφp φb μ 𝓕 hμ h𝓕)
          (integrableOn_mul_comp S T hψ hφc hφp b μ 𝓕 hμ h𝓕)
      rw [h2, h1, sub_zero]
      rfl
    rw [e, zero_add]
    have hbd : ∀ z ∈ 𝓕, ‖φ z * (φb - b) (z : QO S T)‖ ≤ C * (ε / ((C + 1) * (M + 1))) := by
      intro z _
      rw [norm_mul]
      refine mul_le_mul (hC z) ?_ (norm_nonneg _) hC0
      refine le_trans (ContinuousMap.norm_coe_le_norm _ _) ?_
      rw [← dist_eq_norm]; exact hdist.le
    calc ‖∫ z in 𝓕, φ z * (φb - b) (z : QO S T) ∂μ‖
        ≤ C * (ε / ((C + 1) * (M + 1))) * M := norm_setIntegral_le_of_norm_le_const hfin hbd
      _ ≤ ε := by
          rw [show C * (ε / ((C + 1) * (M + 1))) * M = ε * (C / (C + 1)) * (M / (M + 1)) by
            field_simp]
          have h1 : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have h2 : M / (M + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have h3 : 0 ≤ C / (C + 1) := by positivity
          have h4 : 0 ≤ M / (M + 1) := by positivity
          nlinarith [mul_le_mul h1 h2 h4 zero_le_one]

  have hsq : ∫ z in 𝓕, ‖φ z‖ ^ 2 ∂μ = 0 := by
    have e : (fun z => φ z * conj (φ z)) = fun z => ((‖φ z‖ ^ 2 : ℝ) : ℂ) := by
      funext z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e, integral_complex_ofReal] at hint0
    exact_mod_cast hint0
  have hInt : IntegrableOn (fun z => ‖φ z‖ ^ 2) 𝓕 μ :=
    integrableOn_of_periodic S T (fun z => ‖φ z‖ ^ 2) (hφc.norm.pow 2)
      (fun a z => by rw [hφp]) μ 𝓕 hμ h𝓕
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hInt).1 hsq

  set t : Set (MO S T) := {z | φ z ≠ 0} with ht
  have hto : IsOpen t := isOpen_ne_fun hφc continuous_const
  have ht𝓕 : μ (t ∩ 𝓕) = 0 := by
    have h1 : (μ.restrict 𝓕) t = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      refine measure_mono_null (fun z hz => ?_) hae
      simp only [Set.mem_setOf_eq, Pi.zero_apply]
      intro h0
      exact hz (by simpa using h0)
    rwa [Measure.restrict_apply hto.measurableSet] at h1
  have := Formalism.IndefR.PHeisFC.countable_ratL T S
  have : MeasurableConstVAdd (ratL T S) (MO S T) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (MO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : MO S T) s⟩
  have hinv : ∀ g : ratL T S, g +ᵥ t = t := by
    intro g
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [ht, Set.mem_setOf_eq]
    have := periodic_of S T hφp (-(g : MO S T)) (neg_mem g.2) z
    show φ (-(g : MO S T) + z) ≠ 0 ↔ φ z ≠ 0
    rw [this]
  have ht0 : μ t = 0 := h𝓕.measure_zero_of_invariant t hinv ht𝓕
  have hte : t = ∅ := by
    by_contra hne
    exact (hto.measure_pos μ (Set.nonempty_iff_ne_empty.2 hne)).ne' ht0
  funext z
  by_contra hz
  have : z ∈ t := hz
  rw [hte] at this
  exact this

theorem charComplete_of
    (ha : ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T),
      (∀ γ, ψ (symplO S T x (ratW T S γ)) = 1) → x ∈ ratL T S) : CharComplete D :=
  fun ψ hψ S T => ⟨ha ψ hψ S T, fun μ 𝓕 hμ h𝓕 φ hφc hφp hcoef =>
    charCompleteB_of S T hψ (ha ψ hψ S T) μ 𝓕 hμ h𝓕 φ hφc hφp hcoef⟩

end Formalism.IndefR.Fin

end
