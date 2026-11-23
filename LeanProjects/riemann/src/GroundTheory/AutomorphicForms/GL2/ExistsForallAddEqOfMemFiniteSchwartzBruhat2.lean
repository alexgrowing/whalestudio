import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
import GroundTheory.AutomorphicForms.ReductionMeasure

namespace GroundTheory.Automorphic.Adele2

open GroundTheory.Global NumberField IsDedekindDomain MeasureTheory Measure Filter Topology
open scoped NumberField.AdeleRing Matrix nonZeroDivisors Pointwise

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def finiteSchwartzBruhat2 : Submodule ℂ ((Fin 2 → 𝔸ᶠ[K]) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.comp_left (smul_zero c)⟩

theorem mem_finiteSchwartzBruhat2 {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ} :
    f ∈ finiteSchwartzBruhat2 K ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

def finiteMeasure2 : Measure (Fin 2 → 𝔸ᶠ[K]) :=
  Measure.pi fun _ ↦ finiteAdeleMeasure K

instance : (finiteMeasure2 K).IsAddHaarMeasure := by
  unfold finiteMeasure2
  infer_instance

def finiteFourier2 (f : (Fin 2 → 𝔸ᶠ[K]) → ℂ) (y : Fin 2 → 𝔸ᶠ[K]) : ℂ :=
  ∫ x, f x * (finiteAdelicChar K (∑ i, x i * y i) : ℂ) ∂finiteMeasure2 K

variable {K}

def finiteTensor2 (g : Fin 2 → 𝔸ᶠ[K] → ℂ) : (Fin 2 → 𝔸ᶠ[K]) → ℂ :=
  fun x ↦ ∏ i, g i (x i)

theorem finiteTensor2_apply (g : Fin 2 → 𝔸ᶠ[K] → ℂ) (x : Fin 2 → 𝔸ᶠ[K]) :
    finiteTensor2 g x = g 0 (x 0) * g 1 (x 1) :=
  Fin.prod_univ_two _

theorem finiteTensor2_mem {g : Fin 2 → 𝔸ᶠ[K] → ℂ} (hg : ∀ i, g i ∈ finiteSchwartzBruhat K) :
    finiteTensor2 g ∈ finiteSchwartzBruhat2 K := by
  have he : finiteTensor2 g = fun x ↦ g 0 (x 0) * g 1 (x 1) := funext (finiteTensor2_apply g)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact ((hg 0).1.comp_continuous (continuous_apply 0)).mul
      ((hg 1).1.comp_continuous (continuous_apply 1))
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i ↦ (hg i).2.isCompact) fun x hx ↦ ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

def idealFiniteAdeles2 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : AddSubgroup (Fin 2 → 𝔸ᶠ[K]) :=
  AddSubgroup.pi Set.univ fun _ ↦ idealFiniteAdeles I

theorem mem_idealFiniteAdeles2 {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : Fin 2 → 𝔸ᶠ[K]} :
    x ∈ idealFiniteAdeles2 I ↔ ∀ i, x i ∈ idealFiniteAdeles I := by
  simp [idealFiniteAdeles2, AddSubgroup.mem_pi]

theorem coe_idealFiniteAdeles2 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealFiniteAdeles2 I : Set (Fin 2 → 𝔸ᶠ[K])) =
      Set.univ.pi fun _ ↦ (idealFiniteAdeles I : Set 𝔸ᶠ[K]) := by
  ext x
  simp [mem_idealFiniteAdeles2]

theorem isOpen_idealFiniteAdeles2 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsOpen (idealFiniteAdeles2 I : Set (Fin 2 → 𝔸ᶠ[K])) := by
  rw [coe_idealFiniteAdeles2]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_idealFiniteAdeles I

theorem isCompact_idealFiniteAdeles2 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsCompact (idealFiniteAdeles2 I : Set (Fin 2 → 𝔸ᶠ[K])) := by
  rw [coe_idealFiniteAdeles2]
  exact isCompact_univ_pi fun _ ↦ isCompact_idealFiniteAdeles I

theorem exists_idealFiniteAdeles2_subset {W : Set (Fin 2 → 𝔸ᶠ[K])} (hW : W ∈ 𝓝 0) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (idealFiniteAdeles2 I : Set (Fin 2 → 𝔸ᶠ[K])) ⊆ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨J, -, t, ht, hJt⟩ := hW
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : 𝔸ᶠ[K]) := Filter.iInter_mem.mpr fun i ↦ ht i
  obtain ⟨I, hI⟩ := exists_idealFiniteAdeles_subset hU
  refine ⟨I, fun x hx ↦ hJt fun i _ ↦ ?_⟩
  exact Set.mem_iInter.mp (hI ((mem_idealFiniteAdeles2.mp hx) i)) i

open Classical in

theorem finiteTensor2_cosetIndicator_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a x : Fin 2 → 𝔸ᶠ[K]) :
    finiteTensor2 (fun i ↦ cosetIndicator I (a i)) x =
      if x - a ∈ idealFiniteAdeles2 I then 1 else 0 := by
  classical
  rw [finiteTensor2_apply, cosetIndicator_apply, cosetIndicator_apply]
  have h : x - a ∈ idealFiniteAdeles2 I ↔
      x 0 - a 0 ∈ idealFiniteAdeles I ∧ x 1 - a 1 ∈ idealFiniteAdeles I := by
    rw [mem_idealFiniteAdeles2, Fin.forall_fin_two]
    rfl
  by_cases h0 : x 0 - a 0 ∈ idealFiniteAdeles I <;> by_cases h1 : x 1 - a 1 ∈ idealFiniteAdeles I <;>
    simp [h, h0, h1]

theorem exists_forall_add_eq_of_mem_finiteSchwartzBruhat2 {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhat2 K) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ x, ∀ h ∈ idealFiniteAdeles2 I, f (x + h) = f x := by
  have hloc : ∀ x : Fin 2 → 𝔸ᶠ[K], ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ h ∈ idealFiniteAdeles2 J, f (x + h) = f x := by
    intro x
    have h1 : ∀ᶠ h in 𝓝 (0 : Fin 2 → 𝔸ᶠ[K]), f (x + h) = f x :=
      ((continuous_const_add x).tendsto' 0 x (add_zero x)).eventually (hf.1.eventually_eq x)
    obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles2_subset h1
    exact ⟨J, fun h hh ↦ hJ hh⟩
  choose J hJ using hloc
  obtain ⟨t, ht⟩ := hf.2.isCompact.elim_finite_subcover
    (fun x ↦ x +ᵥ (idealFiniteAdeles2 (J x) : Set (Fin 2 → 𝔸ᶠ[K])))
    (fun x ↦ (isOpen_idealFiniteAdeles2 (J x)).vadd x)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_cancel]
      exact zero_mem _⟩)
  have hW : (⋂ x ∈ t, (idealFiniteAdeles2 (J x) : Set (Fin 2 → 𝔸ᶠ[K]))) ∈ 𝓝 0 :=
    (biInter_finset_mem t).mpr fun x _ ↦
      (isOpen_idealFiniteAdeles2 (J x)).mem_nhds (zero_mem _)
  obtain ⟨I, hI⟩ := exists_idealFiniteAdeles2_subset hW
  have hmain : ∀ x ∈ tsupport f, ∀ h ∈ idealFiniteAdeles2 I, f (x + h) = f x := by
    intro x hx h hh
    obtain ⟨x₀, hx₀t, hxx₀⟩ := Set.mem_iUnion₂.mp (ht hx)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, SetLike.mem_coe] at hxx₀
    have hh' : h ∈ idealFiniteAdeles2 (J x₀) := Set.mem_iInter₂.mp (hI hh) x₀ hx₀t
    have e1 := hJ x₀ (x - x₀) hxx₀
    have e2 := hJ x₀ (x + h - x₀) (by
      have : x + h - x₀ = (x - x₀) + h := by abel
      rw [this]
      exact add_mem hxx₀ hh')
    rw [add_sub_cancel] at e1 e2
    rw [e1, e2]
  refine ⟨I, fun x h hh ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hmain x hx h hh
  · by_cases hxh : x + h ∈ tsupport f
    · have := hmain (x + h) hxh (-h) (neg_mem hh)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxh]

theorem exists_eq_sum_finiteTensor2_cosetIndicator {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhat2 K) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : Finset (Fin 2 → 𝔸ᶠ[K])),
      f = ∑ a ∈ s, f a • finiteTensor2 (fun i ↦ cosetIndicator I (a i)) := by
  classical
  obtain ⟨I, hI⟩ := exists_forall_add_eq_of_mem_finiteSchwartzBruhat2 hf
  let H := idealFiniteAdeles2 I
  have : DiscreteTopology ((Fin 2 → 𝔸ᶠ[K]) ⧸ H) :=
    QuotientAddGroup.discreteTopology (isOpen_idealFiniteAdeles2 I)
  have hS : ((QuotientAddGroup.mk : (Fin 2 → 𝔸ᶠ[K]) → (Fin 2 → 𝔸ᶠ[K]) ⧸ H) '' tsupport f).Finite :=
    (hf.2.isCompact.image continuous_quotient_mk').finite_of_discrete
  have hmk : ∀ a x : Fin 2 → 𝔸ᶠ[K], x - a ∈ idealFiniteAdeles2 I ↔
      (QuotientAddGroup.mk x : (Fin 2 → 𝔸ᶠ[K]) ⧸ H) = QuotientAddGroup.mk a := by
    intro a x
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_sub, sub_eq_neg_add]
  have hinj : Set.InjOn (fun q : (Fin 2 → 𝔸ᶠ[K]) ⧸ H ↦ q.out) ↑hS.toFinset :=
    fun q _ q' _ h ↦ by simpa using congrArg (QuotientAddGroup.mk (s := H)) h
  refine ⟨I, hS.toFinset.image fun q ↦ q.out, ?_⟩
  rw [Finset.sum_image hinj]
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finiteTensor2_cosetIndicator_apply, mul_ite, mul_one,
    mul_zero, hmk, QuotientAddGroup.out_eq']
  rw [Finset.sum_ite_eq]
  split_ifs with hx
  · have hq := QuotientAddGroup.out_eq' (s := H) (QuotientAddGroup.mk x)
    rw [← hmk] at hq
    have := hI x (Quotient.out (QuotientAddGroup.mk x : (Fin 2 → 𝔸ᶠ[K]) ⧸ H) - x) hq
    rw [add_sub_cancel] at this
    exact this.symm
  · exact image_eq_zero_of_notMem_tsupport fun hx' ↦ hx ((Set.Finite.mem_toFinset hS).mpr
      ⟨x, hx', rfl⟩)

theorem finiteSchwartzBruhat2_eq_span :
    finiteSchwartzBruhat2 K = Submodule.span ℂ (Set.range fun p : (FractionalIdeal (𝓞 K)⁰ K)ˣ ×
      (Fin 2 → 𝔸ᶠ[K]) ↦ finiteTensor2 fun i ↦ cosetIndicator p.1 (p.2 i)) := by
  refine le_antisymm (fun f hf ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨I, s, hs⟩ := exists_eq_sum_finiteTensor2_cosetIndicator hf
    rw [hs]
    exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(I, a), rfl⟩)
  · rintro _ ⟨p, rfl⟩
    exact finiteTensor2_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat p.1 (p.2 i)

theorem integrable_of_mem_finiteSchwartzBruhat2 {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhat2 K) : Integrable f (finiteMeasure2 K) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem continuous_finiteAdelicChar_sum_mul (y : Fin 2 → 𝔸ᶠ[K]) :
    Continuous fun x : Fin 2 → 𝔸ᶠ[K] ↦ (finiteAdelicChar K (∑ i, x i * y i) : ℂ) :=
  continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const))

theorem integrable_mul_finiteAdelicChar_sum {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hf : Integrable f (finiteMeasure2 K)) (y : Fin 2 → 𝔸ᶠ[K]) :
    Integrable (fun x ↦ f x * (finiteAdelicChar K (∑ i, x i * y i) : ℂ)) (finiteMeasure2 K) :=
  hf.mono (hf.1.mul (continuous_finiteAdelicChar_sum_mul y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem finiteFourier2_add {f g : (Fin 2 → 𝔸ᶠ[K]) → ℂ} (hf : Integrable f (finiteMeasure2 K))
    (hg : Integrable g (finiteMeasure2 K)) :
    finiteFourier2 K (f + g) = finiteFourier2 K f + finiteFourier2 K g := by
  funext y
  simp only [finiteFourier2, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_finiteAdelicChar_sum hf y)
    (integrable_mul_finiteAdelicChar_sum hg y)

theorem finiteFourier2_smul (c : ℂ) (f : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    finiteFourier2 K (c • f) = c • finiteFourier2 K f := by
  funext y
  simp only [finiteFourier2, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem finiteFourier2_zero : finiteFourier2 K (0 : (Fin 2 → 𝔸ᶠ[K]) → ℂ) = 0 := by
  funext y
  simp [finiteFourier2]

theorem finiteFourier2_finiteTensor2 (g : Fin 2 → 𝔸ᶠ[K] → ℂ) :
    finiteFourier2 K (finiteTensor2 g) = finiteTensor2 fun i ↦ finiteFourier K (g i) := by
  funext y
  have h := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 ↦ finiteAdeleMeasure K)
    (fun i x ↦ g i x * (finiteAdelicChar K (x * y i) : ℂ))
  rw [finiteFourier2, finiteTensor2]
  simp only [finiteFourier]
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [finiteTensor2, Fin.prod_univ_two, Fin.sum_univ_two, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  ring

theorem finiteFourier2_finiteTensor2_mem {g : Fin 2 → 𝔸ᶠ[K] → ℂ}
    (hg : ∀ i, g i ∈ finiteSchwartzBruhat K) :
    finiteFourier2 K (finiteTensor2 g) ∈ finiteSchwartzBruhat2 K := by
  rw [finiteFourier2_finiteTensor2]
  exact finiteTensor2_mem fun i ↦ finiteFourier_mem_finiteSchwartzBruhat (hg i)

theorem finiteFourier2_mem {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ} (hf : f ∈ finiteSchwartzBruhat2 K) :
    finiteFourier2 K f ∈ finiteSchwartzBruhat2 K := by
  rw [finiteSchwartzBruhat2_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    exact finiteFourier2_finiteTensor2_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat I (a i)
  | zero => rw [finiteFourier2_zero]; exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhat2_eq_span] at hg hh
    rw [finiteFourier2_add (integrable_of_mem_finiteSchwartzBruhat2 hg)
      (integrable_of_mem_finiteSchwartzBruhat2 hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    rw [finiteFourier2_smul]
    exact Submodule.smul_mem _ c ih

theorem finiteFourier2_finiteFourier2 {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhat2 K) :
    finiteFourier2 K (finiteFourier2 K f) = fun x ↦ f (-x) := by
  rw [finiteSchwartzBruhat2_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    rw [finiteFourier2_finiteTensor2, finiteFourier2_finiteTensor2]
    funext x
    simp only [finiteTensor2, Pi.neg_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [finiteFourier_finiteFourier (cosetIndicator_mem_finiteSchwartzBruhat I (a i))]
  | zero => funext x; simp [finiteFourier2_zero]
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhat2_eq_span] at hg hh
    rw [finiteFourier2_add (integrable_of_mem_finiteSchwartzBruhat2 hg)
        (integrable_of_mem_finiteSchwartzBruhat2 hh),
      finiteFourier2_add
        (integrable_of_mem_finiteSchwartzBruhat2 (finiteFourier2_mem hg))
        (integrable_of_mem_finiteSchwartzBruhat2 (finiteFourier2_mem hh)), ihg, ihh]
    rfl
  | smul c g _ ih =>
    rw [finiteFourier2_smul, finiteFourier2_smul, ih]
    rfl

def finiteVecMulHomeomorph (g : GL (Fin 2) 𝔸ᶠ[K]) : (Fin 2 → 𝔸ᶠ[K]) ≃ₜ (Fin 2 → 𝔸ᶠ[K]) where
  toFun x := x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])
  invFun x := x ᵥ* ((g⁻¹ : GL (Fin 2) 𝔸ᶠ[K]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])
  left_inv x := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  right_inv x := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.vecMul_one]
  continuous_toFun := continuous_id.matrix_vecMul continuous_const
  continuous_invFun := continuous_id.matrix_vecMul continuous_const

theorem comp_vecMul_mem_finiteSchwartzBruhat2 (g : GL (Fin 2) 𝔸ᶠ[K])
    {f : (Fin 2 → 𝔸ᶠ[K]) → ℂ} (hf : f ∈ finiteSchwartzBruhat2 K) :
    (fun x ↦ f (x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]))) ∈ finiteSchwartzBruhat2 K :=
  ⟨hf.1.comp_continuous (finiteVecMulHomeomorph g).continuous,
    hf.2.comp_homeomorph (finiteVecMulHomeomorph g)⟩

end

end GroundTheory.Automorphic.Adele2
