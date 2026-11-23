import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsFrames
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Filter Topology

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem holoOn_mono {U V : Set X} {f : X → ℂ} (h : A.HoloOn U f) (hVU : V ⊆ U) : A.HoloOn V f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_const (U : Set X) (c : ℂ) : A.HoloOn U (fun _ => c) := fun _ _ _ => analyticAt_const

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U (fun y => f y * g y) := fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_div {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) (h0 : ∀ y ∈ U, g y ≠ 0) :
    A.HoloOn U (fun y => f y / g y) := fun j z hz => (hf j z hz).div (hg j z hz) (h0 _ hz.2)

theorem holoOn_pow {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) (m : ℕ) : A.HoloOn U (fun y => f y ^ m) :=
  fun j z hz => (hf j z hz).pow m

theorem holoOn_prod {U : Set X} {ι : Type} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, A.HoloOn U (f i)) :
    A.HoloOn U (fun y => ∏ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h1 := holoOn_mul A (hf i (Finset.mem_insert_self i s)) (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h1

theorem holo_continuousAt {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x :=
  PositivityTheory.Xgp.c_bm_exists_frames.continuousAt_of_holoOn A hf hx

theorem holo_continuousOn {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) : ContinuousOn f U :=
  fun _ hx => (holo_continuousAt A hf hx).continuousWithinAt

theorem holoOn_coord {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := fun j z hz =>
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt _).comp ((hψ j).1 z hz)

theorem exists_coords_ne (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {O : Set X} (hO : IsOpen O) {y : X}
    (hy : y ∈ O) (hyψ : y ∈ ψ.source) : ∃ y' ∈ O ∩ ψ.source, ∀ i, ψ y' i ≠ 0 := by
  have hD : Dense (Set.pi Set.univ fun _ : Fin e => ({0}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun _ _ => dense_compl_singleton 0
  have hopen : IsOpen (ψ '' (ψ.source ∩ O)) := ψ.isOpen_image_source_inter hO
  obtain ⟨t, ⟨y', ⟨hy'ψ, hy'O⟩, rfl⟩, ht⟩ := hD.inter_open_nonempty _ hopen ⟨ψ y, y, ⟨hyψ, hy⟩, rfl⟩
  exact ⟨y', ⟨hy'O, hy'ψ⟩, fun i => ht i (Set.mem_univ i)⟩

theorem eqOn_of_coords_ne {β : Type} [NormedAddCommGroup β] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {O : Set X} (hO : IsOpen O) (hOψ : O ⊆ ψ.source) {f g : X → β} (hf : ContinuousOn f O) (hg : ContinuousOn g O)
    (h : ∀ y ∈ O, (∀ i, ψ y i ≠ 0) → f y = g y) : ∀ y ∈ O, f y = g y := by
  intro y hy
  by_contra hne
  have hopen : IsOpen (O ∩ (fun z => f z - g z) ⁻¹' {0}ᶜ) :=
    (hf.sub hg).isOpen_inter_preimage hO isOpen_compl_singleton
  obtain ⟨y', ⟨⟨hy'O, hy'ne⟩, -⟩, hc⟩ := exists_coords_ne ψ hopen ⟨hy, sub_ne_zero.2 hne⟩ (hOψ hy)
  exact hy'ne (sub_eq_zero.2 (h y' hy'O hc))

end Holo

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_smul_homog {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) (c : K → ℂ)
    (z : (Σ k, J k) → ℂ) : eval (fun p => c p.1 * z p) G = (∏ k, c k ^ a k) * eval z G := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ k, c k ^ a k) * ∏ p, z p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hG d hd k]
  rw [h1]
  ring

theorem eval_map_conj (G : MvPolynomial (Σ k, J k) ℂ) (z : (Σ k, J k) → ℂ) :
    eval z (map (starRingEnd ℂ) G) = starRingEnd ℂ (eval (fun p => starRingEnd ℂ (z p)) G) := by
  rw [MvPolynomial.eval_map, show ∀ w, MvPolynomial.eval w G = eval₂ (RingHom.id ℂ) w G from fun w => rfl,
    MvPolynomial.eval₂_comp_left,
    RingHom.comp_id]
  congr 1
  funext p
  simp

theorem isMultiHomog_map_conj {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) :
    IsMultiHomog (map (starRingEnd ℂ) G) a := fun m hm => hG m (support_map_subset _ _ hm)

noncomputable def nd (a : K → ℕ) (z : (Σ k, J k) → ℂ) : ℝ := ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k

theorem nd_smul (a : K → ℕ) (c : K → ℂ) (z : (Σ k, J k) → ℂ) :
    nd a (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (2 * a k)) * nd a z := by
  unfold nd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    simp [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, mul_pow, ← pow_mul]

theorem nd_conj (a : K → ℕ) (z : (Σ k, J k) → ℂ) : nd a (fun p => starRingEnd ℂ (z p)) = nd a z := by
  simp [nd]

theorem nd_pos (a : K → ℕ) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < nd a z := by
  refine Finset.prod_pos fun k _ => pow_pos ?_ _
  obtain ⟨i, hi⟩ := hz k
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem continuous_nd (a : K → ℕ) : Continuous (nd (J := J) a) :=
  continuous_finsetProd _ fun k _ =>
    (continuous_finsetSum _ fun i _ => (continuous_norm.comp (continuous_apply _)).pow 2).pow _

theorem term_smul {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    ‖eval (fun p => c p.1 * z p) G‖ ^ 2 / nd a (fun p => c p.1 * z p) = ‖eval z G‖ ^ 2 / nd a z := by
  rw [eval_smul_homog hG, nd_smul, norm_mul, mul_pow, norm_prod]
  have h1 : (∏ k, ‖c k ^ a k‖) ^ 2 = ∏ k, ‖c k‖ ^ (2 * a k) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, ← pow_mul, mul_comm]
  have hne : (∏ k, ‖c k‖ ^ (2 * a k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [h1, mul_div_mul_left _ _ hne]

end Forms

end PositivityTheory.Xgp.c_bm_exists_boundary
