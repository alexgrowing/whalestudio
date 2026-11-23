import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace StokesOffDiscriminant

variable {n D : ℕ}

open Classical in

def sheetTerm (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin D) (Fin n) ℂ)
    (H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ) (y : Fin D → ℂ) (x : Fin n → ℂ) : ℝ :=
  (fibre J A y).indicator (fun x => if h : ∃ s, IsSheetAt J A x s then H x h.choose else 0) x

theorem sheetSum_eq_finsum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin D) (Fin n) ℂ)
    (H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ) (y : Fin D → ℂ) :
    sheetSum J A H y = ∑ᶠ x, sheetTerm J A H y x := by
  unfold sheetSum sheetTerm
  rw [finsum_mem_def]

theorem window_of_sheet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    ∃ (V : Set (Fin D → ℂ)) (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ x ∈ W ∧
      DifferentiableOn ℂ s V ∧ (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
  obtain ⟨V, hV, hxV, hsd, hsx, hsec, N, hN, hNs⟩ := hs
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  refine ⟨V, interior N ∩ (fun z => A *ᵥ z) ⁻¹' V, hV, isOpen_interior.inter (hV.preimage hAc),
    ⟨mem_interior_iff_mem_nhds.2 hN, hxV⟩, hsd, hsec, ?_⟩
  rintro x' ⟨hx'Z, hx'N, hx'V⟩
  have hx's : s (A *ᵥ x') = x' := (hNs x' ⟨hx'Z, interior_subset hx'N⟩ hx'V).symm
  exact ⟨hx'V, V, hV, hx'V, hsd, hx's, hsec, interior N, isOpen_interior.mem_nhds hx'N,
    fun x'' hx'' hAx'' => hNs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩

open Classical in

theorem sheetTerm_window {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ} {y : Fin D → ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s)
    (h1 : ∀ x s', A *ᵥ x = y → IsSheetAt J A x s' → IsSheetAt J A x s → H x s' = H x s)
    (h2 : ∀ x s', x ∈ zeroSet J → A *ᵥ x = y → x ∉ W → IsSheetAt J A x s' → H x s' = 0)
    (h3 : y ∈ V → s y ∉ W → H (s y) s = 0) (x : Fin n → ℂ) :
    sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0 := by
  unfold sheetTerm
  by_cases hx : x ∈ fibre J A y
  · rw [Set.indicator_of_mem hx]
    obtain ⟨hxZ, hxy⟩ := hx
    by_cases hxW : x ∈ W
    · obtain ⟨hAV, hsx⟩ := hW x ⟨hxZ, hxW⟩
      have hxs : s (A *ᵥ x) = x := hsx.choose_spec.2.2.2.1
      have hyV : y ∈ V := hxy ▸ hAV
      have hx' : x = s y := by rw [← hxy, hxs]
      have hex : ∃ s', IsSheetAt J A x s' := ⟨s, hsx⟩
      rw [dif_pos hex, if_pos ⟨hyV, hx'⟩, h1 x _ hxy hex.choose_spec hsx, ← hx']
    · have h0 : (if h : ∃ s', IsSheetAt J A x s' then H x h.choose else 0) = 0 := by
        split_ifs with hex
        · exact h2 x _ hxZ hxy hxW hex.choose_spec
        · rfl
      rw [h0]
      split_ifs with hc
      · obtain ⟨hyV, rfl⟩ := hc
        exact (h3 hyV hxW).symm
      · rfl
  · rw [Set.indicator_of_notMem hx]
    split_ifs with hc
    · obtain ⟨hyV, rfl⟩ := hc
      exact absurd ⟨(hsec y hyV).2, (hsec y hyV).1⟩ hx
    · rfl

open Classical in
theorem finite_support_sheetTerm_window {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin D) (Fin n) ℂ} {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ}
    {y : Fin D → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (h : ∀ x, sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0) :
    (Function.support (sheetTerm J A H y)).Finite := by
  refine (Set.finite_singleton (s y)).subset fun x hx => ?_
  rw [Function.mem_support, h x] at hx
  split_ifs at hx with hc
  · exact hc.2
  · exact absurd rfl hx

open Classical in
theorem sheetSum_window {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ} {y : Fin D → ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (h : ∀ x, sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0) :
    sheetSum J A H y = V.indicator (fun y => H (s y) s) y := by
  rw [sheetSum_eq_finsum, finsum_congr h]
  by_cases hyV : y ∈ V
  · rw [Set.indicator_of_mem hyV, finsum_eq_single _ (s y) fun x hx => if_neg fun hc => hx hc.2]
    simp [hyV]
  · rw [Set.indicator_of_notMem hyV]
    simp [hyV]

theorem sheetSum_finset_sum {ι : Type*} (t : Finset ι) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin D) (Fin n) ℂ} {y : Fin D → ℂ}
    (H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ)
    (K : ι → (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ)
    (hH : ∀ x ∈ fibre J A y, ∀ s', IsSheetAt J A x s' → H x s' = ∑ i ∈ t, K i x s')
    (hfin : ∀ i ∈ t, (Function.support (sheetTerm J A (K i) y)).Finite) :
    sheetSum J A H y = ∑ i ∈ t, sheetSum J A (K i) y := by
  simp only [sheetSum_eq_finsum]
  rw [← finsum_sum_comm t (fun x i => sheetTerm J A (K i) y x) hfin]
  refine finsum_congr fun x => ?_
  unfold sheetTerm
  by_cases hx : x ∈ fibre J A y
  · simp only [Set.indicator_of_mem hx]
    split_ifs with hex
    · exact hH x hx _ hex.choose_spec
    · simp
  · simp [Set.indicator_of_notMem hx]

theorem hessC_fam_cons {m : ℕ} (f : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) :
    (fun k => ReciprocityTheory.AnForm.hessC ((Fin.cons f φ : Fin (m + 1) → (Fin (m + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (ReciprocityTheory.AnForm.hessC f z) (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp

theorem maDens_cons_add {m : ℕ} (f g : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fun w => f w + g w) φ) z =
      ReciprocityTheory.AnForm.maDens (Fin.cons f φ) z + ReciprocityTheory.AnForm.maDens (Fin.cons g φ) z := by
  unfold ReciprocityTheory.AnForm.maDens
  rw [hessC_fam_cons, hessC_fam_cons, hessC_fam_cons, ReciprocityTheory.AnForm.A.hessC_add f g z hf hg,
    ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum,
    ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum]
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]
  ring

theorem maDens_cons_finset_sum {m : ℕ} {ι : Type*} (t : Finset ι)
    (g : ι → (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ) (z : Fin (m + 1) → ℂ)
    (hg : ∀ i ∈ t, ContDiffAt ℝ 2 (g i) z) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fun w => ∑ i ∈ t, g i w) φ) z =
      ∑ i ∈ t, ReciprocityTheory.AnForm.maDens (Fin.cons (g i) φ) z := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ReciprocityTheory.AnForm.M.PLAux.maDens_cons_eq_zero EventuallyEq.rfl
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [maDens_cons_add (g a) (fun w => ∑ i ∈ t, g i w) φ z (hg a (Finset.mem_insert_self a t))
      (ContDiffAt.sum fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem fam_comp {m : ℕ} {α β : Type*} (f : α → ℝ) (φ : Fin m → α → ℝ) (s : β → α) :
    (fun k => vecCons f φ k ∘ s) = (Fin.cons (f ∘ s) (fun k => φ k ∘ s) : Fin (m + 1) → β → ℝ) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem maDens_eq_zero_of_notMem_tsupport {m : ℕ} (f : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) {s : (Fin (m + 1) → ℂ) → Fin n → ℂ} {y : Fin (m + 1) → ℂ}
    (hs : ContinuousAt s y) (hy : s y ∉ tsupport f) :
    ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y = 0 := by
  rw [fam_comp]
  apply ReciprocityTheory.AnForm.M.PLAux.maDens_cons_eq_zero
  filter_upwards [hs.preimage_mem_nhds ((isClosed_tsupport f).isOpen_compl.mem_nhds hy)] with w hw
  exact image_eq_zero_of_notMem_tsupport (f := f) (x := s w) hw

theorem maDens_sheet_congr {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    (Ψ : Fin D → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ} {s s' : (Fin D → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (hs' : IsSheetAt J A x s') :
    ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) (A *ᵥ x) :=
  ReciprocityTheory.AnForm.M.PLAux.maDens_congr_germ fun k =>
    (SheetSumMeasurable.sheet_eventuallyEq hs hs').fun_comp (Ψ k)

theorem continuousAt_sheet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    ContinuousAt s (A *ᵥ x) := by
  obtain ⟨V, hV, hxV, hsd, -⟩ := hs
  exact hsd.continuousOn.continuousAt (hV.mem_nhds hxV)

theorem analyticOnNhd_of_differentiableOn {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) : AnalyticOnNhd ℂ s V := fun y hy =>
  analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood D V (fun y => s y j) hV (differentiableOn_pi.1 hsd j) y hy

theorem contDiffOn_comp_section {J : Ideal (MvPolynomial (Fin n) ℂ)} {g : (Fin n → ℂ) → ℝ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} (hg : SmoothNear (zeroSet J) g)
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) (hsZ : ∀ y ∈ V, s y ∈ zeroSet J) :
    ContDiffOn ℝ ∞ (g ∘ s) V := by
  obtain ⟨O, -, hZO, hgO⟩ := hg
  exact hgO.comp (ReciprocityTheory.AnForm.M.pa_holoSmooth s V (analyticOnNhd_of_differentiableOn hV hsd))
    fun y hy => hZO (hsZ y hy)

open Classical in

theorem sheetTerm_weight_window {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (Ψ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin D → ℂ) (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => f x * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then f (s y) * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) y else 0 := by
  have hf0 : ∀ x, x ∉ W → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfW h)
  refine sheetTerm_window hsec hW ?_ ?_ ?_ x
  · rintro x s' rfl hs' hs
    rw [maDens_sheet_congr Ψ hs hs']
  · intro x s' _ _ hxW _
    rw [hf0 x hxW, zero_mul]
  · intro _ hyW
    rw [hf0 _ hyW, zero_mul]

open Classical in

theorem sheetTerm_cons_window {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (D + 1)) (Fin n) ℂ} {s : (Fin (D + 1) → ℂ) → Fin n → ℂ}
    {V : Set (Fin (D + 1) → ℂ)} {W : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hsd : DifferentiableOn ℂ s V) (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f G : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (φ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then G (s y) * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y
      else 0 := by
  refine sheetTerm_window hsec hW ?_ ?_ ?_ x
  · rintro x s' rfl hs' hs
    rw [maDens_sheet_congr (vecCons f φ) hs hs']
  · rintro x s' _ rfl hxW hs'
    have hx : s' (A *ᵥ x) = x := hs'.choose_spec.2.2.2.1
    rw [maDens_eq_zero_of_notMem_tsupport f φ (continuousAt_sheet hs')
      (by rw [hx]; exact fun h => hxW (hfW h)), mul_zero]
  · intro hyV hyW
    rw [maDens_eq_zero_of_notMem_tsupport f φ (hsd.continuousOn.continuousAt (hV.mem_nhds hyV))
      (fun h => hyW (hfW h)), mul_zero]

theorem contDiffAt_comp_sheet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {g : (Fin n → ℂ) → ℝ} {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ}
    (hg : SmoothNear (zeroSet J) g) (hs : IsSheetAt J A x s) : ContDiffAt ℝ 2 (g ∘ s) (A *ᵥ x) := by
  obtain ⟨V, hV, hxV, hsd, -, hsec, -⟩ := hs
  exact ((contDiffOn_comp_section hg hV hsd fun y hy => (hsec y hy).2).contDiffAt
    (hV.mem_nhds hxV)).of_le (WithTop.coe_le_coe.2 le_top)

theorem maDens_sheet_finset_sum {ι : Type*} (t : Finset ι) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (D + 1)) (Fin n) ℂ} (F : (Fin n → ℂ) → ℝ) (f : ι → (Fin n → ℂ) → ℝ)
    (φ : Fin D → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ} {s : (Fin (D + 1) → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (hsum : ∀ z ∈ zeroSet J, F z = ∑ i ∈ t, f i z)
    (hf : ∀ i ∈ t, SmoothNear (zeroSet J) (f i)) :
    ReciprocityTheory.AnForm.maDens (fun k => vecCons F φ k ∘ s) (A *ᵥ x) =
      ∑ i ∈ t, ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s) (A *ᵥ x) := by
  simp only [fam_comp]
  rw [ReciprocityTheory.AnForm.M.PLAux.maDens_congr_germ
    (ψ := Fin.cons (fun w => ∑ i ∈ t, (f i ∘ s) w) (fun k => φ k ∘ s)) ?_]
  · exact maDens_cons_finset_sum t (fun i => f i ∘ s) _ _ fun i hi => contDiffAt_comp_sheet (hf i hi) hs
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.cons_zero]
      obtain ⟨V, hV, hxV, -, -, hsec, -⟩ := hs
      filter_upwards [hV.mem_nhds hxV] with w hw
      exact hsum _ (hsec w hw).2
    · simp only [Fin.cons_succ]
      exact EventuallyEq.rfl

theorem window_stokes {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (D + 1)) (Fin n) ℂ}
    {s : (Fin (D + 1) → ℂ) → Fin n → ℂ} {V : Set (Fin (D + 1) → ℂ)} {W : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f G : (Fin n → ℂ) → ℝ)
    (φ : Fin D → (Fin n → ℂ) → ℝ) (hf : SmoothNear (zeroSet J) f) (hG : SmoothNear (zeroSet J) G)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (hfc : HasCompactSupport f) (hfW : tsupport f ⊆ W) :
    chartInt J A f (vecCons G φ) = chartInt J A G (vecCons f φ) ∧
      Integrable (chartDens J A f (vecCons G φ)) ∧ Integrable (chartDens J A G (vecCons f φ)) := by
  have hsZ : ∀ y ∈ V, s y ∈ zeroSet J := fun y hy => (hsec y hy).2
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hvV : ContDiffOn ℝ ∞ (V.indicator (f ∘ s)) V :=
    (contDiffOn_comp_section hf hV hsd hsZ).congr fun y hy => Set.indicator_of_mem hy _
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hCc : IsCompact ((fun x => A *ᵥ x) '' (tsupport f ∩ zeroSet J)) :=
    (hfc.inter_right (SheetSumMeasurable.isClosed_zeroSet J)).image hAc
  have hCV : (fun x => A *ᵥ x) '' (tsupport f ∩ zeroSet J) ⊆ V := by
    rintro _ ⟨x, ⟨hxf, hxZ⟩, rfl⟩
    exact (hW x ⟨hxZ, hfW hxf⟩).1
  have hvC : tsupport (V.indicator (f ∘ s)) ⊆ (fun x => A *ᵥ x) '' (tsupport f ∩ zeroSet J) := by
    refine closure_minimal (fun y hy => ?_) hCc.isClosed
    by_cases hyV : y ∈ V
    · rw [Function.mem_support, Set.indicator_of_mem hyV] at hy
      exact ⟨s y, ⟨subset_tsupport f hy, hsZ y hyV⟩, (hsec y hyV).1⟩
    · exact absurd (Set.indicator_of_notMem hyV _) hy
  have hyp : ReciprocityTheory.AnForm.A.PartsHyp (fun k => φ k ∘ s) (V.indicator (f ∘ s)) (G ∘ s) V :=
    ⟨hV, hvV.of_le h3, hCc.of_isClosed_subset (isClosed_tsupport _) hvC, hvC.trans hCV,
      (contDiffOn_comp_section hG hV hsd hsZ).of_le h3,
      fun i => (contDiffOn_comp_section (hφ i) hV hsd hsZ).of_le h3⟩
  obtain ⟨i1, i2, -, -, hsym⟩ := ReciprocityTheory.AnForm.A.parts_thm D _ _ _ V hyp
  have hL : chartDens J A f (vecCons G φ) = V.indicator (fun z => V.indicator (f ∘ s) z *
      ReciprocityTheory.AnForm.maDens (Fin.cons (G ∘ s) (fun k => φ k ∘ s)) z) := by
    funext y
    rw [chartDens, sheetSum_window (sheetTerm_weight_window hsec hW f hfW _ y)]
    by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyV, Set.indicator_of_mem hyV, Set.indicator_of_mem hyV, fam_comp]
      rfl
    · rw [Set.indicator_of_notMem hyV, Set.indicator_of_notMem hyV]
  have hR : chartDens J A G (vecCons f φ) = V.indicator (fun z => (G ∘ s) z *
      ReciprocityTheory.AnForm.maDens (Fin.cons (V.indicator (f ∘ s)) (fun k => φ k ∘ s)) z) := by
    funext y
    rw [chartDens, sheetSum_window (sheetTerm_cons_window hV hsd hsec hW f G hfW φ y)]
    by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyV, Set.indicator_of_mem hyV, fam_comp]
      congr 1
      refine ReciprocityTheory.AnForm.M.PLAux.maDens_congr_germ fun k => ?_
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Fin.cons_zero]
        filter_upwards [hV.mem_nhds hyV] with z hz
        rw [Set.indicator_of_mem hz]
      · simp only [Fin.cons_succ]
        exact EventuallyEq.rfl
    · rw [Set.indicator_of_notMem hyV, Set.indicator_of_notMem hyV]
  refine ⟨?_, ?_, ?_⟩
  · unfold chartInt
    rw [hL, hR, integral_indicator hV.measurableSet, integral_indicator hV.measurableSet]
    exact hsym.symm
  · rw [hL]
    exact (integrable_indicator_iff hV.measurableSet).2 i1
  · rw [hR]
    exact (integrable_indicator_iff hV.measurableSet).2 i2

end StokesOffDiscriminant

end

end GroundTheory.Heights₂.Heights
