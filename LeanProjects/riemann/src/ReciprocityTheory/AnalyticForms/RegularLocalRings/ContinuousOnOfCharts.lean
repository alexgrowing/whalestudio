import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemBasicOpenSecHomIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LiftChartIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem sep_of_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U) {x y : X} (hx : x ∈ U)
    (hy : y ∈ U) (hne : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
  obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ := t2_separation hne
  refine ⟨U ∩ f ⁻¹' a, U ∩ f ⁻¹' b, hf.isOpen_inter_preimage hU ha, hf.isOpen_inter_preimage hU hb,
    ⟨hx, hxa⟩, ⟨hy, hyb⟩, ?_⟩
  exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hab hz.2 hz'.2

def blkNorm (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : ℝ :=
  Complex.normSq (z q) / ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩)

theorem blkNorm_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) :
    blkNorm z q = blkNorm z' q := by
  obtain ⟨a, ha, rfl⟩ := h
  have hq : Complex.normSq (a q.1) ≠ 0 := by simpa using ha q.1
  simp only [blkNorm, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem blkNorm_ne_zero_iff (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : blkNorm z q ≠ 0 ↔ z q ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [blkNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (z q) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (z q) ≤ ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩) :=
      Finset.single_le_sum (f := fun j => Complex.normSq (z ⟨q.1, j⟩))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ q.2)
    exact (div_pos h1 (h1.trans_le h2)).ne'

def vecNorm {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : ℝ :=
  Complex.normSq (v l) / ∑ k, Complex.normSq (v k)

theorem vecNorm_smul {m : ℕ} {v v' : Fin m → ℂ} (a : ℂ) (ha : a ≠ 0) (h : ∀ k, v k = a * v' k)
    (l : Fin m) : vecNorm v l = vecNorm v' l := by
  have hq : Complex.normSq a ≠ 0 := by simpa using ha
  simp only [vecNorm, h, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem vecNorm_ne_zero_iff {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : vecNorm v l ≠ 0 ↔ v l ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [vecNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (v l) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (v l) ≤ ∑ k, Complex.normSq (v k) :=
      Finset.single_le_sum (f := fun k => Complex.normSq (v k))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ l)
    exact (div_pos h1 (h1.trans_le h2)).ne'

namespace WData

attribute [local instance] WData.lft

variable (w : WData P D hP)

theorem coord_eq_of_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.coord c x = (w.pres c.1 c.2).coord x.1 hx :=
  dif_pos hx

theorem continuousOn_coord (c : w.Idx) : ContinuousOn (w.coord c) (w.src c) := by
  rw [continuousOn_iff']
  intro O hO
  refine ⟨w.src c ∩ w.coord c ⁻¹' O, TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

theorem continuousOn_of_charts {Y : Type*} [TopologicalSpace Y] (U : Set w.M) (f : w.M → Y)
    (h : ∀ x ∈ U, ∃ c, x ∈ w.src c ∧ w.src c ⊆ U ∧ ∃ F : (Fin (w.pres c.1 c.2).n → ℂ) → Y,
      Continuous F ∧ ∀ y ∈ w.src c, f y = F (w.coord c y)) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨c, hxc, -, F, hF, hfF⟩ := h x hx
  have h1 : ContinuousOn (F ∘ w.coord c) (w.src c) := hF.comp_continuousOn (w.continuousOn_coord c)
  have h2 : ContinuousOn f (w.src c) := h1.congr fun y hy => hfF y hy
  exact (h2.continuousAt ((w.isOpen_alt_bis c).mem_nhds hxc)).continuousWithinAt

def lv (c : w.Idx) (x : w.M) : (Σ k, ι k) → ℂ := fun q => eval (w.coord c x) (w.lift c q)

theorem lv_self (c : w.Idx) (x : w.M) (k : K) : w.lv c x ⟨k, c.1 k⟩ = 1 := by
  simp [lv, lift]

theorem one_le_sum_lv (c : w.Idx) (x : w.M) (k : K) :
    1 ≤ ∑ j : ι k, Complex.normSq (w.lv c x ⟨k, j⟩) := by
  have h2 := Finset.single_le_sum (f := fun j => Complex.normSq (w.lv c x ⟨k, j⟩))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ (c.1 k))
  simp only [lv_self, map_one] at h2
  exact h2

def ch (x : w.M) : w.Idx := (w.cover x).choose

theorem mem_ch (x : w.M) : x ∈ w.src (w.ch x) := (w.cover x).choose_spec

def blk (q : Σ k, ι k) (x : w.M) : ℝ := blkNorm (w.lv (w.ch x) x) q

theorem blk_eq (q : Σ k, ι k) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.blk q x = blkNorm (w.lv c x) q :=
  blkNorm_of_sameOrbit (w.compat (w.ch x) c x ⟨w.mem_ch x, hx⟩) q

theorem continuous_blk (q : Σ k, ι k) : Continuous (w.blk q) := by
  rw [← continuousOn_univ]
  refine w.continuousOn_of_charts _ _ fun x _ => ⟨w.ch x, w.mem_ch x, Set.subset_univ _, ?_⟩
  set c := w.ch x
  refine ⟨fun v => Complex.normSq (eval v (w.lift c q)) /
    max 1 (∑ j : ι q.1, Complex.normSq (eval v (w.lift c ⟨q.1, j⟩))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _)).div
      (continuous_const.max (continuous_finsetSum _ fun j _ =>
        Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.lv c y q) / max 1 (∑ j : ι q.1, Complex.normSq (w.lv c y ⟨q.1, j⟩))
    rw [w.blk_eq q c y hy, blkNorm, max_eq_right (w.one_le_sum_lv c y q.1)]

def tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) : Fin (w.m p) → ℂ :=
  fun k => w.coord ⟨p, i⟩ x (w.yt p i k)

theorem tv_eq_val (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩)
    (k : Fin (w.m p)) : w.tv p i x k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hx := by
  have h := (w.pres p i).eval_coord_eq_val x.1 hx x.2 (X (w.yt p i k))
  rw [eval_X, w.sec_yt] at h
  rw [tv, w.coord_eq_of_mem ⟨p, i⟩ x hx]
  exact h

theorem val_t_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) :
    val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi =
      val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hj * val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi := by
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨hi, hj⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) ((w.pres p i).V ⊓ (w.pres p j).V) x.1 hij x.2
  have h := congrArg φ (w.t_cocycle p i j k)
  rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h
  exact h.symm

theorem val_t_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M)
    (hi : x ∈ w.src ⟨p, i⟩) :
    val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  have h1 := val_eq_zero_iff (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi x.2
  have h2 := Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := w.W) x.1 hi (w.t p i j)
  have h3 : x.1 ∈ w.W.basicOpen (w.t p i j) ↔ x ∈ w.src ⟨p, j⟩ := by
    rw [← w.inter p i j, TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
  exact (h1.not.trans h2).trans h3

theorem tv_self (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x i = 1 := by
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) (w.pres p i).V x.1 hx x.2
  rw [w.tv_eq_val p i x hx, ← hφ, w.t_self, map_one]

theorem tv_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x j ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  rw [w.tv_eq_val p i x hi]
  exact w.val_t_ne_zero_iff p i j x hi

theorem tv_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) : w.tv p i x k = w.tv p i x j * w.tv p j x k := by
  rw [w.tv_eq_val p i x hi, w.tv_eq_val p i x hi, w.tv_eq_val p j x hj, w.val_t_mul p i j x hi hj k,
    mul_comm]

theorem one_le_sum_tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    1 ≤ ∑ k, Complex.normSq (w.tv p i x k) := by
  have h2 := Finset.single_le_sum (f := fun k => Complex.normSq (w.tv p i x k))
    (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  simp only [w.tv_self p i x hx, map_one] at h2
  exact h2

def overP (p : (k : K) → ι k) : Set w.M := {x | ∃ i, x ∈ w.src ⟨p, i⟩}

theorem isOpen_overP (p : (k : K) → ι k) : IsOpen (w.overP p) := by
  have h : w.overP p = ⋃ i, w.src ⟨p, i⟩ := by
    ext x
    simp [overP]
  rw [h]
  exact isOpen_iUnion fun i => w.isOpen_alt_bis _

open Classical in

def fib (p : (k : K) → ι k) (l : Fin (w.m p)) (x : w.M) : ℝ :=
  if h : ∃ i, x ∈ w.src ⟨p, i⟩ then vecNorm (w.tv p h.choose x) l else 0

theorem fib_eq (p : (k : K) → ι k) (l : Fin (w.m p)) (i : Fin (w.m p)) (x : w.M)
    (hx : x ∈ w.src ⟨p, i⟩) : w.fib p l x = vecNorm (w.tv p i x) l := by
  have h : ∃ i, x ∈ w.src ⟨p, i⟩ := ⟨i, hx⟩
  rw [fib, dif_pos h]
  exact vecNorm_smul _ ((w.tv_ne_zero_iff p _ i x h.choose_spec).mpr hx)
    (fun k => w.tv_mul p _ i x h.choose_spec hx k) l

theorem continuousOn_fib (p : (k : K) → ι k) (l : Fin (w.m p)) :
    ContinuousOn (w.fib p l) (w.overP p) := by
  refine w.continuousOn_of_charts _ _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨p, i⟩, hi, fun y hy => ⟨i, hy⟩, ?_⟩
  refine ⟨fun v => Complex.normSq (v (w.yt p i l)) /
    max 1 (∑ k, Complex.normSq (v (w.yt p i k))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (continuous_apply _)).div
      (continuous_const.max (continuous_finsetSum _ fun k _ =>
        Complex.continuous_normSq.comp (continuous_apply _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.tv p i y l) / max 1 (∑ k, Complex.normSq (w.tv p i y k))
    rw [w.fib_eq p l i y hy, vecNorm, max_eq_right (w.one_le_sum_tv p i y hy)]

end WData

end

end ReciprocityTheory.AnForm.R
