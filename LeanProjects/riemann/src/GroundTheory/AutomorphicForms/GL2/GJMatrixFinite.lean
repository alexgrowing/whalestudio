import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
import GroundTheory.AutomorphicForms.ReductionMeasure

namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.Global NumberField IsDedekindDomain MeasureTheory Measure Filter Topology
open scoped NumberField.AdeleRing nonZeroDivisors Pointwise

noncomputable section

section Generic

variable {X : Type*} [AddCommGroup X]

def cosetInd (H : AddSubgroup X) (a : X) : X → ℂ :=
  fun x ↦ by classical exact if x - a ∈ H then 1 else 0

theorem cosetInd_apply (H : AddSubgroup X) (a x : X) [Decidable (x - a ∈ H)] :
    cosetInd H a x = if x - a ∈ H then 1 else 0 := by
  unfold cosetInd
  congr 1

variable [TopologicalSpace X] [IsTopologicalAddGroup X] {𝓗 : Set (AddSubgroup X)}

theorem exists_mem_forall_add_eq (hopen : ∀ H ∈ 𝓗, IsOpen (H : Set X))
    (hbasis : ∀ W ∈ 𝓝 (0 : X), ∃ H ∈ 𝓗, (H : Set X) ⊆ W) {f : X → ℂ}
    (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ H ∈ 𝓗, ∀ x, ∀ h ∈ H, f (x + h) = f x := by
  have hloc : ∀ x : X, ∃ J ∈ 𝓗, ∀ h ∈ J, f (x + h) = f x := by
    intro x
    have h1 : ∀ᶠ h in 𝓝 (0 : X), f (x + h) = f x :=
      ((continuous_const_add x).tendsto' 0 x (add_zero x)).eventually (hlc.eventually_eq x)
    obtain ⟨J, hJ𝓗, hJ⟩ := hbasis _ h1
    exact ⟨J, hJ𝓗, fun h hh ↦ hJ hh⟩
  choose J hJ𝓗 hJ using hloc
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover
    (fun x ↦ x +ᵥ (J x : Set X))
    (fun x ↦ (hopen _ (hJ𝓗 x)).vadd x)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_cancel]
      exact zero_mem _⟩)
  have hW : (⋂ x ∈ t, (J x : Set X)) ∈ 𝓝 0 :=
    (biInter_finset_mem t).mpr fun x _ ↦ (hopen _ (hJ𝓗 x)).mem_nhds (zero_mem _)
  obtain ⟨I, hI𝓗, hI⟩ := hbasis _ hW
  have hmain : ∀ x ∈ tsupport f, ∀ h ∈ I, f (x + h) = f x := by
    intro x hx h hh
    obtain ⟨x₀, hx₀t, hxx₀⟩ := Set.mem_iUnion₂.mp (ht hx)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, SetLike.mem_coe] at hxx₀
    have hh' : h ∈ J x₀ := Set.mem_iInter₂.mp (hI hh) x₀ hx₀t
    have e1 := hJ x₀ (x - x₀) hxx₀
    have e2 := hJ x₀ (x + h - x₀) (by
      have : x + h - x₀ = (x - x₀) + h := by abel
      rw [this]
      exact add_mem hxx₀ hh')
    rw [add_sub_cancel] at e1 e2
    rw [e1, e2]
  refine ⟨I, hI𝓗, fun x h hh ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hmain x hx h hh
  · by_cases hxh : x + h ∈ tsupport f
    · have := hmain (x + h) hxh (-h) (neg_mem hh)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxh]

theorem exists_eq_sum_cosetInd {H : AddSubgroup X} (hH : IsOpen (H : Set X)) {f : X → ℂ}
    (hcs : HasCompactSupport f) (hI : ∀ x, ∀ h ∈ H, f (x + h) = f x) :
    ∃ s : Finset X, f = ∑ a ∈ s, f a • cosetInd H a := by
  classical
  have : DiscreteTopology (X ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hS : ((QuotientAddGroup.mk : X → X ⧸ H) '' tsupport f).Finite :=
    (hcs.isCompact.image continuous_quotient_mk').finite_of_discrete
  have hmk : ∀ a x : X, x - a ∈ H ↔
      (QuotientAddGroup.mk x : X ⧸ H) = QuotientAddGroup.mk a := by
    intro a x
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_sub, sub_eq_neg_add]
  have hinj : Set.InjOn (fun q : X ⧸ H ↦ q.out) ↑hS.toFinset :=
    fun q _ q' _ h ↦ by simpa using congrArg (QuotientAddGroup.mk (s := H)) h
  refine ⟨hS.toFinset.image fun q ↦ q.out, ?_⟩
  rw [Finset.sum_image hinj]
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, cosetInd_apply, mul_ite, mul_one, mul_zero, hmk,
    QuotientAddGroup.out_eq']
  rw [Finset.sum_ite_eq]
  split_ifs with hx
  · have hq := QuotientAddGroup.out_eq' (s := H) (QuotientAddGroup.mk x)
    rw [← hmk] at hq
    have := hI x (Quotient.out (QuotientAddGroup.mk x : X ⧸ H) - x) hq
    rw [add_sub_cancel] at this
    exact this.symm
  · exact image_eq_zero_of_notMem_tsupport fun hx' ↦ hx ((Set.Finite.mem_toFinset hS).mpr
      ⟨x, hx', rfl⟩)

omit [IsTopologicalAddGroup X] in

theorem exists_pi_subset {ι : Type*} [Finite ι]
    (hbasis : ∀ W ∈ 𝓝 (0 : X), ∃ H ∈ 𝓗, (H : Set X) ⊆ W) {W : Set (ι → X)} (hW : W ∈ 𝓝 0) :
    ∃ H ∈ 𝓗, (AddSubgroup.pi Set.univ (fun _ : ι ↦ H) : Set (ι → X)) ⊆ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨J, -, t, ht, hJt⟩ := hW
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : X) := Filter.iInter_mem.mpr fun i ↦ ht i
  obtain ⟨H, hH𝓗, hH⟩ := hbasis _ hU
  refine ⟨H, hH𝓗, fun x hx ↦ hJt fun i _ ↦ ?_⟩
  exact Set.mem_iInter.mp (hH (((AddSubgroup.mem_pi _).mp hx) i (Set.mem_univ i))) i

omit [TopologicalSpace X] [IsTopologicalAddGroup X] in

theorem prod_cosetInd {ι : Type*} [Fintype ι] (H : AddSubgroup X) (a x : ι → X) :
    ∏ i, cosetInd H (a i) (x i) = cosetInd (AddSubgroup.pi Set.univ fun _ : ι ↦ H) a x := by
  classical
  simp only [cosetInd_apply, Finset.prod_boole, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
    Pi.sub_apply, Finset.mem_univ]

theorem exists_eq_sum_prod_cosetInd {ι : Type*} [Fintype ι]
    (hopen : ∀ H ∈ 𝓗, IsOpen (H : Set X))
    (hbasis : ∀ W ∈ 𝓝 (0 : X), ∃ H ∈ 𝓗, (H : Set X) ⊆ W) {f : (ι → X) → ℂ}
    (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ H ∈ 𝓗, ∃ s : Finset (ι → X), f = ∑ a ∈ s, f a • fun x ↦ ∏ i, cosetInd H (a i) (x i) := by
  have hopen' : ∀ P ∈ (fun H ↦ AddSubgroup.pi Set.univ fun _ : ι ↦ H) '' 𝓗,
      IsOpen (P : Set (ι → X)) := by
    rintro _ ⟨H, hH, rfl⟩
    rw [AddSubgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ ↦ hopen H hH
  have hbasis' : ∀ W ∈ 𝓝 (0 : ι → X), ∃ P ∈ (fun H ↦ AddSubgroup.pi Set.univ fun _ : ι ↦ H) '' 𝓗,
      (P : Set (ι → X)) ⊆ W := by
    intro W hW
    obtain ⟨H, hH, hHW⟩ := exists_pi_subset hbasis hW
    exact ⟨_, ⟨H, hH, rfl⟩, hHW⟩
  obtain ⟨_, ⟨H, hH, rfl⟩, hinv⟩ := exists_mem_forall_add_eq hopen' hbasis' hlc hcs
  obtain ⟨s, hs⟩ := exists_eq_sum_cosetInd (hopen' _ ⟨H, hH, rfl⟩) hcs hinv
  refine ⟨H, hH, s, hs.trans (Finset.sum_congr rfl fun a _ ↦ ?_)⟩
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, prod_cosetInd]

end Generic

variable (K : Type*) [Field K] [NumberField K] {ι : Type*} [Fintype ι]

def finiteSchwartzBruhatPi : Submodule ℂ ((ι → 𝔸ᶠ[K]) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.comp_left (smul_zero c)⟩

omit [Fintype ι] in
theorem mem_finiteSchwartzBruhatPi {f : (ι → 𝔸ᶠ[K]) → ℂ} :
    f ∈ finiteSchwartzBruhatPi K ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

def finiteMeasurePi : Measure (ι → 𝔸ᶠ[K]) :=
  Measure.pi fun _ ↦ finiteAdeleMeasure K

instance : (finiteMeasurePi K (ι := ι)).IsAddHaarMeasure := by
  unfold finiteMeasurePi
  infer_instance

def finiteFourierPi (f : (ι → 𝔸ᶠ[K]) → ℂ) (y : ι → 𝔸ᶠ[K]) : ℂ :=
  ∫ x, f x * (finiteAdelicChar K (∑ i, x i * y i) : ℂ) ∂finiteMeasurePi K

variable {K}

def finiteTensor (g : ι → 𝔸ᶠ[K] → ℂ) : (ι → 𝔸ᶠ[K]) → ℂ :=
  fun x ↦ ∏ i, g i (x i)

theorem finiteTensor_mem {g : ι → 𝔸ᶠ[K] → ℂ} (hg : ∀ i, g i ∈ finiteSchwartzBruhat K) :
    finiteTensor g ∈ finiteSchwartzBruhatPi K := by
  refine ⟨?_, ?_⟩
  · have : finiteTensor g = ∏ i, fun x : ι → 𝔸ᶠ[K] ↦ g i (x i) := by
      funext x
      simp only [finiteTensor, Finset.prod_apply]
    rw [this]
    exact Finset.prod_induction _ IsLocallyConstant (fun _ _ ha hb ↦ ha.mul hb)
      (IsLocallyConstant.const 1) fun i _ ↦ (hg i).1.comp_continuous (continuous_apply i)
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i ↦ (hg i).2.isCompact) fun x hx ↦ ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

theorem cosetIndicator_eq_cosetInd (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : 𝔸ᶠ[K]) :
    cosetIndicator J a = cosetInd (idealFiniteAdeles J) a := by
  classical
  funext x
  rw [cosetIndicator_apply, cosetInd_apply]

theorem finiteSchwartzBruhatPi_eq_span :
    finiteSchwartzBruhatPi K (ι := ι) = Submodule.span ℂ (Set.range fun p :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ × (ι → 𝔸ᶠ[K]) ↦ finiteTensor fun i ↦ cosetIndicator p.1 (p.2 i)) := by
  refine le_antisymm (fun f hf ↦ ?_) (Submodule.span_le.mpr ?_)
  · have hopen : ∀ H ∈ Set.range (idealFiniteAdeles (K := K)), IsOpen (H : Set 𝔸ᶠ[K]) := by
      rintro _ ⟨J, rfl⟩
      exact isOpen_idealFiniteAdeles J
    have hbasis : ∀ W ∈ 𝓝 (0 : 𝔸ᶠ[K]), ∃ H ∈ Set.range (idealFiniteAdeles (K := K)),
        (H : Set 𝔸ᶠ[K]) ⊆ W := by
      intro W hW
      obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hW
      exact ⟨_, ⟨J, rfl⟩, hJ⟩
    obtain ⟨_, ⟨J, rfl⟩, s, hs⟩ := exists_eq_sum_prod_cosetInd hopen hbasis hf.1 hf.2
    rw [hs]
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨(J, a), ?_⟩)
    funext x
    simp only [finiteTensor, cosetIndicator_eq_cosetInd]
  · rintro _ ⟨p, rfl⟩
    exact finiteTensor_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat p.1 (p.2 i)

theorem integrable_of_mem_finiteSchwartzBruhatPi {f : (ι → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhatPi K) : Integrable f (finiteMeasurePi K) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

omit [NumberField K] in

theorem addChar_sum {G κ : Type*} [AddCommMonoid G] (χ : AddChar G Circle) (s : Finset κ)
    (a : κ → G) : (χ (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (χ (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, ih, Finset.prod_insert hj]

theorem continuous_finiteAdelicChar_sum_mul (y : ι → 𝔸ᶠ[K]) :
    Continuous fun x : ι → 𝔸ᶠ[K] ↦ (finiteAdelicChar K (∑ i, x i * y i) : ℂ) :=
  continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const))

theorem integrable_mul_finiteAdelicChar_sum {f : (ι → 𝔸ᶠ[K]) → ℂ}
    (hf : Integrable f (finiteMeasurePi K)) (y : ι → 𝔸ᶠ[K]) :
    Integrable (fun x ↦ f x * (finiteAdelicChar K (∑ i, x i * y i) : ℂ)) (finiteMeasurePi K) :=
  hf.mono (hf.1.mul (continuous_finiteAdelicChar_sum_mul y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem finiteFourierPi_add {f g : (ι → 𝔸ᶠ[K]) → ℂ} (hf : Integrable f (finiteMeasurePi K))
    (hg : Integrable g (finiteMeasurePi K)) :
    finiteFourierPi K (f + g) = finiteFourierPi K f + finiteFourierPi K g := by
  funext y
  simp only [finiteFourierPi, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_finiteAdelicChar_sum hf y)
    (integrable_mul_finiteAdelicChar_sum hg y)

theorem finiteFourierPi_smul (c : ℂ) (f : (ι → 𝔸ᶠ[K]) → ℂ) :
    finiteFourierPi K (c • f) = c • finiteFourierPi K f := by
  funext y
  simp only [finiteFourierPi, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem finiteFourierPi_zero : finiteFourierPi K (0 : (ι → 𝔸ᶠ[K]) → ℂ) = 0 := by
  funext y
  simp [finiteFourierPi]

theorem finiteFourierPi_finiteTensor (g : ι → 𝔸ᶠ[K] → ℂ) :
    finiteFourierPi K (finiteTensor g) = finiteTensor fun i ↦ finiteFourier K (g i) := by
  funext y
  have h := integral_fintype_prod_eq_prod (μ := fun _ : ι ↦ finiteAdeleMeasure K)
    (fun i x ↦ g i x * (finiteAdelicChar K (x * y i) : ℂ))
  rw [finiteFourierPi, finiteTensor]
  simp only [finiteFourier]
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [finiteTensor]
  rw [addChar_sum (finiteAdelicChar K) Finset.univ fun i ↦ x i * y i, ← Finset.prod_mul_distrib]

theorem finiteFourierPi_mem {f : (ι → 𝔸ᶠ[K]) → ℂ} (hf : f ∈ finiteSchwartzBruhatPi K) :
    finiteFourierPi K f ∈ finiteSchwartzBruhatPi K := by
  rw [finiteSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    rw [finiteFourierPi_finiteTensor]
    exact finiteTensor_mem fun i ↦
      finiteFourier_mem_finiteSchwartzBruhat (cosetIndicator_mem_finiteSchwartzBruhat I (a i))
  | zero => rw [finiteFourierPi_zero]; exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhatPi_eq_span] at hg hh
    rw [finiteFourierPi_add (integrable_of_mem_finiteSchwartzBruhatPi hg)
      (integrable_of_mem_finiteSchwartzBruhatPi hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    rw [finiteFourierPi_smul]
    exact Submodule.smul_mem _ c ih

theorem finiteFourierPi_finiteFourierPi {f : (ι → 𝔸ᶠ[K]) → ℂ}
    (hf : f ∈ finiteSchwartzBruhatPi K) :
    finiteFourierPi K (finiteFourierPi K f) = fun x ↦ f (-x) := by
  rw [finiteSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    rw [finiteFourierPi_finiteTensor, finiteFourierPi_finiteTensor]
    funext x
    simp only [finiteTensor, Pi.neg_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [finiteFourier_finiteFourier (cosetIndicator_mem_finiteSchwartzBruhat I (a i))]
  | zero => funext x; simp [finiteFourierPi_zero]
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhatPi_eq_span] at hg hh
    rw [finiteFourierPi_add (integrable_of_mem_finiteSchwartzBruhatPi hg)
        (integrable_of_mem_finiteSchwartzBruhatPi hh),
      finiteFourierPi_add
        (integrable_of_mem_finiteSchwartzBruhatPi (finiteFourierPi_mem hg))
        (integrable_of_mem_finiteSchwartzBruhatPi (finiteFourierPi_mem hh)), ihg, ihh]
    rfl
  | smul c g _ ih =>
    rw [finiteFourierPi_smul, finiteFourierPi_smul, ih]
    rfl

end

end GroundTheory.Automorphic.GJMatrix
