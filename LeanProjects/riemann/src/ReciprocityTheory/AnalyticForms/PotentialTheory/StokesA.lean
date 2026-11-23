import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_smooth_continuous (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j).continuousOn.continuousAt (by
      rw [Set.preimage_univ, Set.inter_univ]
      exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem st_smooth_mul (A : FinHolAtlas e X) {f g : X → ℝ} (hf : A.Smooth f) (hg : A.Smooth g) :
    A.Smooth (fun x => f x * g x) := fun j => (hf j).mul (hg j)

theorem st_smooth_const (A : FinHolAtlas e X) (c : ℝ) : A.Smooth (fun _ => c) := fun j => contDiffOn_const

theorem st_smooth_sum (A : FinHolAtlas e X) {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ m, A.Smooth (f m)) : A.Smooth (fun x => ∑ m ∈ s, f m x) := fun j => ContDiffOn.sum fun m _ => hf m j

theorem st_mInt_congr_phi (A : FinHolAtlas e X) {Φ Ψ : Fin e → LocPot X}
    (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  have h1 : ∀ j y, locDens A Φ j y = locDens A Ψ j y := fun j y => by
    unfold locDens; simp only [h]
  unfold mInt integralWith
  simp only [h1]

theorem st_mInt_zero (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt integralWith
  split_ifs <;> simp

theorem st_hessC_eq_zero {D : ℕ} {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (c : ℝ)
    (h : f =ᶠ[𝓝 y] fun _ => c) : hessC f y = 0 := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun _ : Fin D → ℂ => c) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => c)) y :=
    h1.fderiv_eq
  have h3 : fderiv ℝ (fun _ : Fin D → ℂ => c) = fun _ => 0 := by
    funext z; simp
  ext i k
  simp only [hessC, h2, h3]
  simp

theorem st_maDens_cons_eq_zero {n : ℕ} (φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (h : hessC (φ 0) y = 0) : maDens φ y = 0 := by
  have hm : (fun k => hessC (φ k) y) =
      (Fin.cons (hessC (φ 0) y) (fun i : Fin n => hessC (φ i.succ) y) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDens, hm, h, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum]
  simp

theorem st_locDens_cons_eq_zero (A : FinHolAtlas (e + 1) X) (k : Fin A.n) (ψ : X → ℝ)
    (Φ : Fin e → LocPot X) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart k).target)
    (hψ : (A.chart k).symm y ∉ tsupport ψ) :
    locDens A (Fin.cons (LocPot.ofFun ψ) Φ) k y = 0 := by
  unfold locDens
  apply st_maDens_cons_eq_zero
  apply st_hessC_eq_zero 0
  have h1 : (tsupport ψ)ᶜ ∈ 𝓝 ((A.chart k).symm y) := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ
  have h2 := ((A.chart k).continuousAt_symm hy).preimage_mem_nhds h1
  filter_upwards [h2] with y' hy'
  first
  | exact image_eq_zero_of_notMem_tsupport hy'
  | exact image_eq_zero_of_nmem_tsupport hy'

theorem st_mIntConstPot (A : FinHolAtlas (e + 1) X) (c : ℝ) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  unfold mInt integralWith
  split_ifs
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : ∀ y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y = 0 := by
      intro y
      unfold locDens
      apply st_maDens_cons_eq_zero
      exact st_hessC_eq_zero c (Filter.Eventually.of_forall fun _ => rfl)
    simp [h0]
  · rfl

theorem st_isPotential_cons (A : FinHolAtlas (e + 1) X) {u : X → ℝ} (hu : A.Smooth u)
    {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · show IsPotential A (LocPot.ofFun u)
    exact ⟨fun x => hu, fun x x' y _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
      fun j => analyticOnNhd_const, fun z _ => by simp [LocPot.ofFun]⟩⟩
  · show IsPotential A (Φ i)
    exact hΦ i

theorem st_mInt_finset_sum [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, Continuous (f m)) :
    mInt A Φ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Φ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mInt_zero A Φ
  | insert a s ha ih =>
    have hc : Continuous (fun x => ∑ m ∈ s, f m x) := continuous_finsetSum _ fun m _ => hf m
    have := mIntLinear A Φ hΦ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Φ hΦ _ (hf a)) (mIntegrableCont A Φ hΦ _ hc)
    simp only [one_mul] at this
    simp only [Finset.sum_insert ha, this, ih]

theorem st_mInt_cons_finset_sum [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) (g : X → ℝ) (hg : Continuous g) :
    mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g =
      ∑ m ∈ s, mInt A (Fin.cons (LocPot.ofFun (f m)) Φ) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mIntConstPot A 0 Φ g
  | insert a s ha ih =>
    have hS : A.Smooth (fun x => ∑ m ∈ s, f m x) := st_smooth_sum A s hf
    have hcongr : mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ insert a s, f m x) Φ) g =
        mInt A (Fin.cons (LocPot.ofFun (f a) + LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g := by
      apply st_mInt_congr_phi
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · funext x y
        simp [Finset.sum_insert ha, LocPot.ofFun]
        rfl
      · rfl
    rw [hcongr, mIntAdd A _ _ Φ (isPotential_ofFun A _ (hf a)) (isPotential_ofFun A _ hS) hΦ g
      (mIntegrableCont A _ (st_isPotential_cons A (hf a) hΦ) g hg)
      (mIntegrableCont A _ (st_isPotential_cons A hS hΦ) g hg), ih, Finset.sum_insert ha]

end

end ReciprocityTheory.AnForm.M
