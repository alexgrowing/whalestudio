import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology

namespace GlobalTheory

section Weight

variable {κ X : Type*}

noncomputable def lwP₂ (S : Finset κ) (z : κ → ℂ) : ℝ :=
  1 + ∑ j ∈ S, |Real.log ‖z j‖|

def coordDivisor (S : Finset κ) (w : X → κ → ℂ) : Set X :=
  {x | ∃ j ∈ S, w x j = 0}

theorem notMem_coordDivisor {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∉ coordDivisor S w ↔ ∀ j ∈ S, w x j ≠ 0 := by
  simp [coordDivisor]

theorem mem_coordDivisor_iff_prod_eq_zero {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∈ coordDivisor S w ↔ ∏ j ∈ S, w x j = 0 := by
  simp [coordDivisor, Finset.prod_eq_zero_iff]

theorem isClosed_coordDivisor [TopologicalSpace X] (S : Finset κ) {w : X → κ → ℂ}
    (hw : ∀ j ∈ S, Continuous fun x => w x j) : IsClosed (coordDivisor S w) := by
  have : coordDivisor S w = {x | ∏ j ∈ S, w x j = 0} :=
    Set.ext fun _ => mem_coordDivisor_iff_prod_eq_zero
  rw [this]
  exact isClosed_eq (continuous_finset_prod S hw) continuous_const

theorem one_le_logWeight (S : Finset κ) (z : κ → ℂ) : 1 ≤ lwP₂ S z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logWeight_pos (S : Finset κ) (z : κ → ℂ) : 0 < lwP₂ S z :=
  one_pos.trans_le (one_le_logWeight S z)

theorem abs_log_norm_le_logWeight {S : Finset κ} (z : κ → ℂ) {j : κ} (hj : j ∈ S) :
    |Real.log ‖z j‖| ≤ lwP₂ S z :=
  (Finset.single_le_sum (f := fun j => |Real.log ‖z j‖|) (fun _ _ => abs_nonneg _) hj).trans
    (le_add_of_nonneg_left zero_le_one)

theorem mul_logWeight_pow_le (S : Finset κ) (z : κ → ℂ) {C C' : ℝ} {N N' : ℕ} (hC : C ≤ C')
    (hC' : 0 ≤ C') (hN : N ≤ N') : C * lwP₂ S z ^ N ≤ C' * lwP₂ S z ^ N' :=
  mul_le_mul hC (pow_le_pow_right₀ (one_le_logWeight S z) hN)
    (pow_nonneg (logWeight_pos S z).le _) hC'

end Weight

section Polydisc

variable {ι : Type*}

end Polydisc

section Growth

variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

def HasLogGrowth (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (f : X → E) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ x ∈ K, x ∉ coordDivisor S w →
    ‖f x‖ ≤ C * lwP₂ S (w x) ^ N

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowth

theorem exists_one_le {f : X → E} (hf : HasLogGrowth S w U f) {K : Set X} (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
      ‖f x‖ ≤ C * lwP₂ S (w x) ^ N := by
  obtain ⟨C, N, h⟩ := hf K hKU hK
  exact ⟨max C 1, N, le_max_right _ _, fun x hx hB => (h x hx hB).trans
    (mul_logWeight_pow_le _ _ (le_max_left _ _) (zero_le_one.trans (le_max_right _ _)) le_rfl)⟩

theorem mono {f : X → E} (hf : HasLogGrowth S w U f) {V : Set X} (hV : V ⊆ U) :
    HasLogGrowth S w V f :=
  fun K hK => hf K (hK.trans hV)

theorem of_norm_le {f : X → E} {g : X → F} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ ‖g x‖) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, N, hC⟩ := hg K hKU hK
  exact ⟨C, N, fun x hx hB => (h x (hKU hx) hB).trans (hC x hx hB)⟩

theorem of_le {f : X → E} {g : X → ℝ} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => (h x hx hB).trans (le_abs_self _)

theorem congr {f g : X → E} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → f x = g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => by rw [h x hx hB]

theorem norm {f : X → E} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => ‖f x‖ :=
  hf.of_norm_le fun _ _ _ => (norm_norm _).le

theorem of_continuousOn {f : X → E} (hf : ContinuousOn f U) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  exact ⟨C, 0, fun x hx _ => by simpa using hC x hx⟩

theorem const (c : E) : HasLogGrowth S w U fun _ => c :=
  of_continuousOn continuousOn_const

theorem lwP₂ : HasLogGrowth S w U fun x => lwP₂ S (w x) :=
  fun _ _ _ => ⟨1, 1, fun x _ _ => by simp [abs_of_pos (logWeight_pos S (w x))]⟩

theorem log_norm {j : κ} (hj : j ∈ S) : HasLogGrowth S w U fun x => Real.log ‖w x j‖ :=
  lwP₂.of_le fun x _ _ => abs_log_norm_le_logWeight (w x) hj

theorem add {f g : X → E} (hf : HasLogGrowth S w U f) (hg : HasLogGrowth S w U g) :
    HasLogGrowth S w U fun x => f x + g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C + D, max N M, fun x hx hB => (norm_add_le _ _).trans ?_⟩
  rw [add_mul]
  exact add_le_add
    ((hC x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_left _ _)))
    ((hD x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_right _ _)))

theorem neg {f : X → E} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => -f x :=
  hf.of_norm_le fun _ _ _ => (norm_neg _).le

theorem sub {f g : X → E} (hf : HasLogGrowth S w U f) (hg : HasLogGrowth S w U g) :
    HasLogGrowth S w U fun x => f x - g x :=
  (hf.add hg.neg).congr fun _ _ _ => sub_eq_add_neg _ _

theorem sum {α : Type*} {s : Finset α} {f : α → X → E} (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) :
    HasLogGrowth S w U fun x => ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem mul {R : Type*} [SeminormedRing R] {f g : X → R} (hf : HasLogGrowth S w U f)
    (hg : HasLogGrowth S w U g) : HasLogGrowth S w U fun x => f x * g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C * D, N + M, fun x hx hB => (norm_mul_le _ _).trans ?_⟩
  rw [pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hC x hx hB) (hD x hx hB) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx hB))

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] {c : X → 𝕜} {f : X → E}
    (hc : HasLogGrowth S w U c) (hf : HasLogGrowth S w U f) :
    HasLogGrowth S w U fun x => c x • f x :=
  (hc.norm.mul hf.norm).of_le fun _ _ _ => (norm_smul _ _).le

theorem prod {R α : Type*} [SeminormedCommRing R] {s : Finset α} {f : α → X → R}
    (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) : HasLogGrowth S w U fun x => ∏ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem pow {R : Type*} [SeminormedRing R] {f : X → R} (hf : HasLogGrowth S w U f) (k : ℕ) :
    HasLogGrowth S w U fun x => f x ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem star {f : X → ℂ} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => star (f x) :=
  hf.of_norm_le fun _ _ _ => (norm_star _).le

theorem comp_of_logWeight {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => GlobalTheory.lwP₂ S (w (π x))) :
    HasLogGrowth S' w' U' fun x => f (π x) := by
  intro K hKU hK
  obtain ⟨C, N, h⟩ := hf (π '' K) (hU.mono_left hKU).image_subset
    (hK.image_of_continuousOn (hπ.mono hKU))
  exact HasLogGrowth.of_le (U := K) ((const C).mul ((hw.mono hKU).pow N))
    (fun x hx hx' => h _ (mem_image_of_mem π hx) (hB x (hKU hx) hx')) K Subset.rfl hK

end HasLogGrowth

def IsUnitMulMonomialOn (S : Finset κ) (v : X' → κ → ℂ) (S' : Finset κ') (w' : X' → κ' → ℂ)
    (U' : Set X') : Prop :=
  ∀ j ∈ S, ∃ (u : X' → ℂ) (m : κ' → ℕ), ContinuousOn u U' ∧
    ∀ x ∈ U', u x ≠ 0 ∧ v x j = u x * ∏ i ∈ S', w' x i ^ m i

namespace IsUnitMulMonomialOn

variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}

theorem notMem (h : IsUnitMulMonomialOn S v S' w' U') {x : X'} (hx : x ∈ U')
    (hB : x ∉ coordDivisor S' w') : x ∉ coordDivisor S v := by
  rw [notMem_coordDivisor] at hB ⊢
  intro j hj
  obtain ⟨u, m, -, hu⟩ := h j hj
  rw [(hu x hx).2]
  exact mul_ne_zero (hu x hx).1 (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hB i hi))

theorem hasLogGrowth_logWeight (h : IsUnitMulMonomialOn S v S' w' U') :
    HasLogGrowth S' w' U' fun x => lwP₂ S (v x) := by
  refine (HasLogGrowth.const 1).add (HasLogGrowth.sum (f := fun j x => |Real.log ‖v x j‖|)
    fun j hj => ?_)
  obtain ⟨u, m, hc, hu⟩ := h j hj
  have h1 : HasLogGrowth S' w' U' fun x => Real.log ‖u x‖ :=
    .of_continuousOn (hc.norm.log fun x hx => norm_ne_zero_iff.2 (hu x hx).1)
  have h2 : HasLogGrowth S' w' U' fun x => ∑ i ∈ S', (m i : ℝ) * Real.log ‖w' x i‖ :=
    .sum (f := fun i x => (m i : ℝ) * Real.log ‖w' x i‖)
      fun i hi => (HasLogGrowth.const _).mul (.log_norm hi)
  refine (h1.add h2).norm.congr fun x hx hB => ?_
  rw [notMem_coordDivisor] at hB
  have h3 : ∀ i ∈ S', ‖w' x i ^ m i‖ ≠ 0 := fun i hi => norm_ne_zero_iff.2 (pow_ne_zero _ (hB i hi))
  rw [(hu x hx).2, norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 (hu x hx).1)
    (Finset.prod_ne_zero_iff.2 h3), Real.log_prod h3]
  simp

end IsUnitMulMonomialOn

theorem HasLogGrowth.comp {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    HasLogGrowth S' w' U' fun x => f (π x) :=
  hf.comp_of_logWeight hπ hU (fun _ hx hB => hw.notMem hx hB) hw.hasLogGrowth_logWeight

end Growth

section Scalar

variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

def IsLogBoundedScalar (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (g : X → ℝ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ ≤ g x ∧ g x ≤ C * lwP₂ S (w x) ^ N

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}

theorem IsLogBoundedScalar.pos (hg : IsLogBoundedScalar S w U g) {x : X} (hx : x ∈ U)
    (hB : x ∉ coordDivisor S w) : 0 < g x := by
  obtain ⟨C, N, hC, h⟩ := hg {x} (singleton_subset_iff.2 hx) isCompact_singleton
  exact (inv_pos.2 (mul_pos hC (pow_pos (logWeight_pos _ _) _))).trans_le (h x rfl hB).1

theorem isLogBoundedScalar_iff : IsLogBoundedScalar S w U g ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x) ∧ HasLogGrowth S w U g ∧
      HasLogGrowth S w U fun x => (g x)⁻¹ := by
  refine ⟨fun h => ⟨fun x => h.pos, fun K hKU hK => ?_, fun K hKU hK => ?_⟩,
    fun ⟨h0, h1, h2⟩ K hKU hK => ?_⟩
  · obtain ⟨C, N, -, h'⟩ := h K hKU hK
    exact ⟨C, N, fun x hx hB => by
      rw [Real.norm_of_nonneg (h.pos (hKU hx) hB).le]; exact (h' x hx hB).2⟩
  · obtain ⟨C, N, hC, h'⟩ := h K hKU hK
    exact ⟨C, N, fun x hx hB => by
      rw [Real.norm_of_nonneg (inv_pos.2 (h.pos (hKU hx) hB)).le]
      exact inv_le_of_inv_le₀ (mul_pos hC (pow_pos (logWeight_pos _ _) _)) (h' x hx hB).1⟩
  · obtain ⟨C, N, hC, h⟩ := (h1.norm.add h2.norm).exists_one_le hKU hK
    refine ⟨C, N, by linarith, fun x hx hB => ?_⟩
    have hp := h0 x (hKU hx) hB
    have hi := inv_pos.2 hp
    have h3 := (le_abs_self _).trans (h x hx hB)
    rw [Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hi.le] at h3
    exact ⟨inv_le_of_inv_le₀ hp (by linarith), by linarith⟩

theorem isLogBoundedScalar_iff_abs_log_le : IsLogBoundedScalar S w U g ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x) ∧ ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ),
      ∀ x ∈ K, x ∉ coordDivisor S w →
        |Real.log (g x)| ≤ C + N * Real.log (lwP₂ S (w x)) := by
  refine ⟨fun h => ⟨fun x => h.pos, fun K hKU hK => ?_⟩, fun ⟨h0, h⟩ K hKU hK => ?_⟩
  · obtain ⟨C, N, hC, h'⟩ := h K hKU hK
    refine ⟨Real.log C, N, fun x hx hB => ?_⟩
    have hw := pow_pos (logWeight_pos S (w x)) N
    rw [← Real.log_pow, ← Real.log_mul hC.ne' hw.ne', abs_le, ← Real.log_inv]
    exact ⟨Real.log_le_log (inv_pos.2 (mul_pos hC hw)) (h' x hx hB).1,
      Real.log_le_log (h.pos (hKU hx) hB) (h' x hx hB).2⟩
  · obtain ⟨C, N, h'⟩ := h K hKU hK
    refine ⟨Real.exp C, N, Real.exp_pos C, fun x hx hB => ?_⟩
    have hw := pow_pos (logWeight_pos S (w x)) N
    have hl := mul_pos (Real.exp_pos C) hw
    have h3 := h' x hx hB
    rw [← Real.log_pow, ← Real.log_exp C, ← Real.log_mul (Real.exp_pos C).ne' hw.ne', abs_le,
      ← Real.log_inv] at h3
    exact ⟨(Real.log_le_log_iff (inv_pos.2 hl) (h0 x (hKU hx) hB)).1 h3.1,
      (Real.log_le_log_iff (h0 x (hKU hx) hB) hl).1 h3.2⟩

namespace IsLogBoundedScalar

theorem hasLogGrowth (hg : IsLogBoundedScalar S w U g) : HasLogGrowth S w U g :=
  (isLogBoundedScalar_iff.1 hg).2.1

theorem hasLogGrowth_inv (hg : IsLogBoundedScalar S w U g) :
    HasLogGrowth S w U fun x => (g x)⁻¹ :=
  (isLogBoundedScalar_iff.1 hg).2.2

theorem mono (hg : IsLogBoundedScalar S w U g) {V : Set X} (hV : V ⊆ U) :
    IsLogBoundedScalar S w V g :=
  fun K hK => hg K (hK.trans hV)

theorem congr (hg : IsLogBoundedScalar S w U g) (h : ∀ x ∈ U, x ∉ coordDivisor S w → g' x = g x) :
    IsLogBoundedScalar S w U g' := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hg K hKU hK
  exact ⟨C, N, hC, fun x hx hB => h x (hKU hx) hB ▸ h' x hx hB⟩

theorem of_continuousOn (hg : ContinuousOn g U) (h0 : ∀ x ∈ U, 0 < g x) :
    IsLogBoundedScalar S w U g :=
  isLogBoundedScalar_iff.2 ⟨fun x hx _ => h0 x hx, .of_continuousOn hg,
    .of_continuousOn (hg.inv₀ fun x hx => (h0 x hx).ne')⟩

theorem const {c : ℝ} (hc : 0 < c) : IsLogBoundedScalar S w U fun _ => c :=
  of_continuousOn continuousOn_const fun _ _ => hc

theorem lwP₂ : IsLogBoundedScalar S w U fun x => lwP₂ S (w x) :=
  fun _ _ _ => ⟨1, 1, one_pos, fun x _ _ => by
    have := one_le_logWeight S (w x)
    simpa using (inv_le_one_of_one_le₀ this).trans this⟩

theorem mul (hg : IsLogBoundedScalar S w U g) (hg' : IsLogBoundedScalar S w U g') :
    IsLogBoundedScalar S w U fun x => g x * g' x :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => mul_pos (hg.pos hx hB) (hg'.pos hx hB),
    hg.hasLogGrowth.mul hg'.hasLogGrowth,
    (hg.hasLogGrowth_inv.mul hg'.hasLogGrowth_inv).congr fun _ _ _ => mul_inv _ _⟩

theorem inv (hg : IsLogBoundedScalar S w U g) : IsLogBoundedScalar S w U fun x => (g x)⁻¹ :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => inv_pos.2 (hg.pos hx hB), hg.hasLogGrowth_inv,
    hg.hasLogGrowth.congr fun _ _ _ => inv_inv _⟩

theorem prod {α : Type*} {s : Finset α} {f : α → X → ℝ}
    (hf : ∀ a ∈ s, IsLogBoundedScalar S w U (f a)) :
    IsLogBoundedScalar S w U fun x => ∏ a ∈ s, f a x :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => Finset.prod_pos fun a ha => (hf a ha).pos hx hB,
    .prod fun a ha => (hf a ha).hasLogGrowth,
    (HasLogGrowth.prod (f := fun a x => (f a x)⁻¹) fun a ha => (hf a ha).hasLogGrowth_inv).congr
      fun _ _ _ => (Finset.prod_inv_distrib _).symm⟩

theorem rpow (hg : IsLogBoundedScalar S w U g) (t : ℝ) :
    IsLogBoundedScalar S w U fun x => g x ^ t := by
  refine isLogBoundedScalar_iff_abs_log_le.2
    ⟨fun x hx hB => Real.rpow_pos_of_pos (hg.pos hx hB) t, fun K hKU hK => ?_⟩
  obtain ⟨C, N, h⟩ := (isLogBoundedScalar_iff_abs_log_le.1 hg).2 K hKU hK
  refine ⟨⌈|t|⌉₊ * C, ⌈|t|⌉₊ * N, fun x hx hB => ?_⟩
  rw [Real.log_rpow (hg.pos (hKU hx) hB), abs_mul, Nat.cast_mul, mul_assoc, ← mul_add]
  exact mul_le_mul (Nat.le_ceil _) (h x hx hB) (abs_nonneg _) (Nat.cast_nonneg _)

theorem zpow (hg : IsLogBoundedScalar S w U g) (k : ℤ) :
    IsLogBoundedScalar S w U fun x => g x ^ k :=
  (hg.rpow k).congr fun _ _ _ => (Real.rpow_intCast _ _).symm

theorem pow (hg : IsLogBoundedScalar S w U g) (k : ℕ) :
    IsLogBoundedScalar S w U fun x => g x ^ k :=
  (hg.rpow k).congr fun _ _ _ => (Real.rpow_natCast _ _).symm

theorem of_pow {k : ℕ} (hk : k ≠ 0) (h0 : ∀ x ∈ U, x ∉ coordDivisor S w → 0 ≤ g x)
    (hg : IsLogBoundedScalar S w U fun x => g x ^ k) : IsLogBoundedScalar S w U g :=
  (hg.rpow (k : ℝ)⁻¹).congr fun x hx hB => (Real.pow_rpow_inv_natCast (h0 x hx hB) hk).symm

theorem comp (hg : IsLogBoundedScalar S w U g) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    IsLogBoundedScalar S' w' U' fun x => g (π x) :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => hg.pos (hU hx) (hw.notMem hx hB),
    hg.hasLogGrowth.comp hπ hU hw, hg.hasLogGrowth_inv.comp hπ hU hw⟩

end IsLogBoundedScalar

end Scalar

section Entries

variable {κ X l m n : Type*} [TopologicalSpace X]

def HasLogGrowthEntries (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (A : X → Matrix m n ℂ) : Prop :=
  ∀ i j, HasLogGrowth S w U fun x => A x i j

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowthEntries

theorem congr {A A' : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → A' x = A x) : HasLogGrowthEntries S w U A' :=
  fun i j => (hA i j).congr fun x hx hB => by rw [h x hx hB]

theorem of_continuousOn {A : X → Matrix m n ℂ} (hA : ContinuousOn A U) :
    HasLogGrowthEntries S w U A :=
  fun i j => .of_continuousOn ((continuous_id.matrix_elem i j).comp_continuousOn hA)

theorem mul [Fintype m] {A : X → Matrix l m ℂ} {A' : X → Matrix m n ℂ}
    (hA : HasLogGrowthEntries S w U A) (hA' : HasLogGrowthEntries S w U A') :
    HasLogGrowthEntries S w U fun x => A x * A' x :=
  fun i j => .sum (f := fun k x => A x i k * A' x k j) fun k _ => (hA i k).mul (hA' k j)

theorem conjTranspose {A : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A) :
    HasLogGrowthEntries S w U fun x => (A x)ᴴ :=
  fun i j => (hA j i).star

theorem transpose {A : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A) :
    HasLogGrowthEntries S w U fun x => (A x)ᵀ :=
  fun i j => hA j i

theorem submatrix {m' n' : Type*} {A : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A)
    (r : m' → m) (c : n' → n) : HasLogGrowthEntries S w U fun x => (A x).submatrix r c :=
  fun i j => hA (r i) (c j)

theorem det [Fintype n] [DecidableEq n] {A : X → Matrix n n ℂ}
    (hA : HasLogGrowthEntries S w U A) : HasLogGrowth S w U fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact .sum (f := fun (σ : Equiv.Perm n) x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A x (σ i) i)
    fun σ _ => (HasLogGrowth.const _).mul
      (.prod (f := fun i x => A x (σ i) i) fun i _ => hA (σ i) i)

theorem trace [Fintype n] {A : X → Matrix n n ℂ} (hA : HasLogGrowthEntries S w U A) :
    HasLogGrowth S w U fun x => (A x).trace :=
  .sum (f := fun i x => A x i i) fun i _ => hA i i

end HasLogGrowthEntries

end Entries

section MatrixLemmas

variable {m n : Type*}

theorem real_smul_one_le_real_smul_one [DecidableEq n] {a b : ℝ} (h : a ≤ b) :
    a • (1 : Matrix n n ℂ) ≤ b • (1 : Matrix n n ℂ) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact PosSemidef.one.smul (sub_nonneg.2 h)

theorem inv_smul_one_le_and_le_smul_one_mono [DecidableEq n] {G : Matrix n n ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (h : a⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ a • (1 : Matrix n n ℂ)) :
    b⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ b • (1 : Matrix n n ℂ) :=
  ⟨(real_smul_one_le_real_smul_one (inv_anti₀ ha hab)).trans h.1,
    h.2.trans (real_smul_one_le_real_smul_one hab)⟩

theorem norm_apply_le_of_le_smul_one [DecidableEq n] {G : Matrix n n ℂ} (hG : G.PosSemidef)
    {a : ℝ} (h : G ≤ a • (1 : Matrix n n ℂ)) (i j : n) : ‖G i j‖ ≤ a := by
  have h1 : ∀ k, (G k k).re ≤ a := fun k => by
    have := (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h).diag_nonneg (i := k))).1
    simpa using this
  have h0 : ∀ k, 0 ≤ (G k k).re := fun k => (Complex.nonneg_iff.1 (hG.diag_nonneg (i := k))).1
  have h2 : ‖G i j‖ ^ 2 ≤ (G i i).re * (G j j).re := norm_sq_apply_le_of_posSemidef hG i j
  have ha : 0 ≤ a := (h0 i).trans (h1 i)
  refine abs_le_of_sq_le_sq' (h2.trans ?_) ha |>.2
  rw [sq]
  exact mul_le_mul (h1 i) (h1 j) (h0 j) ha

variable [Fintype n] [DecidableEq n]

theorem inv_smul_one_le_inv_and_inv_le_smul_one {G : Matrix n n ℂ} {a : ℝ} (ha : 0 < a)
    (h : a⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ a • (1 : Matrix n n ℂ)) :
    a⁻¹ • (1 : Matrix n n ℂ) ≤ G⁻¹ ∧ G⁻¹ ≤ a • (1 : Matrix n n ℂ) := by
  have h0 : (a⁻¹ • (1 : Matrix n n ℂ)).PosDef := PosDef.one.smul (inv_pos.2 ha)
  have h1 := inv_le_inv_of_posDef_of_le (posDef_of_le h0 h.1) h.2
  have h2 := inv_le_inv_of_posDef_of_le h0 h.1
  rw [inv_real_smul_of_posDef PosDef.one ha.ne', inv_one] at h1
  rw [inv_real_smul_of_posDef PosDef.one (inv_pos.2 ha).ne', inv_one, inv_inv] at h2
  exact ⟨h1, h2⟩

variable [Fintype m] [DecidableEq m]

theorem posDef_fromBlocks_zero {A : Matrix m m ℂ} {D : Matrix n n ℂ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  let _ := hA.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ (0 : Matrix m n ℂ) D hA).2 (by simpa using hD.posSemidef)
  rw [conjTranspose_zero] at h
  rw [h.posDef_iff_det_ne_zero, det_fromBlocks_zero₂₁]
  exact mul_ne_zero hA.det_pos.ne' hD.det_pos.ne'

noncomputable def schurComplement₁₁ (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Matrix n n ℂ :=
  G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂

noncomputable def schurComplement₂₂ (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Matrix m m ℂ :=
  G.toBlocks₁₁ - G.toBlocks₁₂ * G.toBlocks₂₂⁻¹ * G.toBlocks₂₁

omit [DecidableEq m] [Fintype m] in

theorem schurComplement₂₂_eq_swap (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    schurComplement₂₂ G = schurComplement₁₁ (G.submatrix Sum.swap Sum.swap) :=
  rfl

theorem schurComplement₁₁_eq_inv {G : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : G.PosDef) :
    schurComplement₁₁ G = (G⁻¹.submatrix Sum.inr Sum.inr)⁻¹ := by
  have h11 : (G.toBlocks₁₁).PosDef := hG.submatrix Sum.inl_injective
  let _ := h11.isUnit.invertible
  let _ := hG.isUnit.invertible
  have h := mul_inv_of_invertible G
  rw [← fromBlocks_toBlocks G⁻¹] at h
  nth_rw 1 [← fromBlocks_toBlocks G] at h
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  refine (inv_eq_left_inv ?_).symm
  change schurComplement₁₁ G * G⁻¹.toBlocks₂₂ = 1
  have h3 : G.toBlocks₁₂ * G⁻¹.toBlocks₂₂ = -(G.toBlocks₁₁ * G⁻¹.toBlocks₁₂) :=
    eq_neg_of_add_eq_zero_right h12
  rw [schurComplement₁₁, Matrix.sub_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, Matrix.mul_assoc,
    ← Matrix.mul_assoc (G.toBlocks₁₁⁻¹), inv_mul_of_invertible, Matrix.one_mul, sub_neg_eq_add,
    add_comm, h22]

omit [DecidableEq n] in

theorem isLeast_schurComplement₁₁ {G : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : G.PosDef) (v : n → ℂ) :
    IsLeast (range fun u : m → ℂ => (star (Sum.elim u v) ⬝ᵥ G *ᵥ Sum.elim u v).re)
      (star v ⬝ᵥ schurComplement₁₁ G *ᵥ v).re := by
  have h11 : (G.toBlocks₁₁).PosDef := hG.submatrix Sum.inl_injective
  let _ := h11.isUnit.invertible
  have h21 : G.toBlocks₂₁ = (G.toBlocks₁₂)ᴴ := by
    ext i j; exact (hG.1.apply _ _).symm
  have key : ∀ u : m → ℂ, star (Sum.elim u v) ⬝ᵥ G *ᵥ Sum.elim u v =
      star (u + (G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v) ⬝ᵥ
        G.toBlocks₁₁ *ᵥ (u + (G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v) +
        star v ⬝ᵥ schurComplement₁₁ G *ᵥ v := by
    intro u
    have := schur_complement_eq₁₁ G.toBlocks₁₂ G.toBlocks₂₂ u v h11.1
    rw [← h21, fromBlocks_toBlocks] at this
    simpa only [dotProduct_mulVec, schurComplement₁₁] using this
  refine ⟨⟨-((G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ v), ?_⟩, ?_⟩
  · simp only [key]
    simp
  · rintro _ ⟨u, rfl⟩
    simp only [key, Complex.add_re, le_add_iff_nonneg_left]
    exact (Complex.nonneg_iff.1 (h11.posSemidef.dotProduct_mulVec_nonneg _)).1

end MatrixLemmas

section PiKronecker

variable {α : Type*} [Fintype α] {l n o : α → Type*}

noncomputable def piKronecker (A : ∀ a, Matrix (l a) (n a) ℂ) : Matrix (∀ a, l a) (∀ a, n a) ℂ :=
  Matrix.of fun i j => ∏ a, A a (i a) (j a)

variable [DecidableEq α] [∀ a, Fintype (n a)]

variable [∀ a, DecidableEq (n a)]

end PiKronecker

section Compound

variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]

noncomputable def compoundMatrix (k : ℕ) (A : Matrix l n ℂ) :
    Matrix (Set.powersetCard l k) (Set.powersetCard n k) ℂ :=
  Matrix.of fun I J => (A.submatrix (subsetEnum I) (subsetEnum J)).det

theorem compoundMatrix_mul [Fintype n] (k : ℕ) (A : Matrix l n ℂ) (A' : Matrix n o ℂ) :
    compoundMatrix k (A * A') = compoundMatrix k A * compoundMatrix k A' := by
  ext I J
  exact det_submatrix_mul_eq_sum_minors A A' _ _

theorem compoundMatrix_conjTranspose (k : ℕ) (A : Matrix l n ℂ) :
    compoundMatrix k Aᴴ = (compoundMatrix k A)ᴴ := by
  ext I J
  simp only [compoundMatrix, of_apply, conjTranspose_apply, ← det_conjTranspose,
    conjTranspose_submatrix]

theorem compoundMatrix_one (k : ℕ) : compoundMatrix k (1 : Matrix n n ℂ) = 1 := by
  ext I J
  rcases eq_or_ne I J with rfl | h
  · rw [one_apply_eq, compoundMatrix, of_apply, submatrix_one _ (subsetEnum_injective I), det_one]
  · rw [one_apply_ne h, compoundMatrix, of_apply]
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h
    have h1 : x ∈ range (subsetEnum I) := by rw [range_subsetEnum]; exact hxI
    have h2 : x ∉ range (subsetEnum J) := by rw [range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

variable [Fintype n]

theorem compoundMatrix_inv (k : ℕ) {A : Matrix n n ℂ} (hA : IsUnit A) :
    (compoundMatrix k A)⁻¹ = compoundMatrix k A⁻¹ := by
  let _ := hA.invertible
  refine inv_eq_left_inv ?_
  rw [← compoundMatrix_mul, inv_mul_of_invertible, compoundMatrix_one]

theorem posDef_compoundMatrix (k : ℕ) {G : Matrix n n ℂ} (hG : G.PosDef) :
    (compoundMatrix k G).PosDef := by
  let _ := hG.isUnit.invertible
  have hu : IsUnit (compoundMatrix k G) := IsUnit.of_mul_eq_one (compoundMatrix k G⁻¹) (by
    rw [← compoundMatrix_mul, mul_inv_of_invertible, compoundMatrix_one])
  refine (PosSemidef.posDef_iff_isUnit ?_).2 hu
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  rw [hC, compoundMatrix_mul, star_eq_conjTranspose, compoundMatrix_conjTranspose]
  exact posSemidef_conjTranspose_mul_self _

end Compound

section LogBounded

variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']

def IsLogBounded [DecidableEq n] (S : Finset κ) (w : X → κ → ℂ) (U : Set X)
    (G : X → Matrix n n ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧
      G x ≤ (C * lwP₂ S (w x) ^ N) • (1 : Matrix n n ℂ)

variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}

theorem IsLogBounded.posDef (hG : IsLogBounded S w U G) {x : X} (hx : x ∈ U)
    (hB : x ∉ coordDivisor S w) : (G x).PosDef := by
  obtain ⟨C, N, hC, h⟩ := hG {x} (singleton_subset_iff.2 hx) isCompact_singleton
  exact posDef_of_le (PosDef.one.smul (inv_pos.2 (mul_pos hC (pow_pos (logWeight_pos _ _) _))))
    (h x rfl hB).1

namespace IsLogBounded

theorem mono (hG : IsLogBounded S w U G) {V : Set X} (hV : V ⊆ U) : IsLogBounded S w V G :=
  fun K hK => hG K (hK.trans hV)

theorem congr (hG : IsLogBounded S w U G) (h : ∀ x ∈ U, x ∉ coordDivisor S w → G' x = G x) :
    IsLogBounded S w U G' := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hG K hKU hK
  exact ⟨C, N, hC, fun x hx hB => h x (hKU hx) hB ▸ h' x hx hB⟩

theorem of_le {g : X → ℝ} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x ∧
      (g x)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧ G x ≤ g x • (1 : Matrix n n ℂ)) :
    IsLogBounded S w U G := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hg.exists_one_le hKU hK
  exact ⟨C, N, by linarith, fun x hx hB => inv_smul_one_le_and_le_smul_one_mono
    (h x (hKU hx) hB).1 ((le_abs_self _).trans (h' x hx hB)) (h x (hKU hx) hB).2⟩

theorem hasLogGrowthEntries (hG : IsLogBounded S w U G) : HasLogGrowthEntries S w U G := by
  intro i j K hKU hK
  obtain ⟨C, N, -, h⟩ := hG K hKU hK
  exact ⟨C, N, fun x hx hB =>
    norm_apply_le_of_le_smul_one (hG.posDef (hKU hx) hB).posSemidef (h x hx hB).2 i j⟩

theorem transpose (hG : IsLogBounded S w U G) : IsLogBounded S w U fun x => (G x)ᵀ := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ⟨?_, ?_⟩⟩
  · simpa using transpose_le_transpose_of_le (h x hx hB).1
  · simpa using transpose_le_transpose_of_le (h x hx hB).2

theorem submatrix (hG : IsLogBounded S w U G) {e : m → n} (he : Function.Injective e) :
    IsLogBounded S w U fun x => (G x).submatrix e e := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ⟨?_, ?_⟩⟩
  · simpa [Matrix.le_iff, submatrix_sub, submatrix_smul, submatrix_one e he] using
      (Matrix.le_iff.1 (h x hx hB).1).submatrix e
  · simpa [Matrix.le_iff, submatrix_sub, submatrix_smul, submatrix_one e he] using
      (Matrix.le_iff.1 (h x hx hB).2).submatrix e

theorem reindex (hG : IsLogBounded S w U G) (e : n ≃ m) :
    IsLogBounded S w U fun x => Matrix.reindex e e (G x) :=
  hG.submatrix e.symm.injective

theorem toBlocks₁₁ {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => (G x).toBlocks₁₁ :=
  hG.submatrix Sum.inl_injective

theorem toBlocks₂₂ {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => (G x).toBlocks₂₂ :=
  hG.submatrix Sum.inr_injective

variable [Fintype n]

theorem inv (hG : IsLogBounded S w U G) : IsLogBounded S w U fun x => (G x)⁻¹ := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  exact ⟨C, N, hC, fun x hx hB => inv_smul_one_le_inv_and_inv_le_smul_one
    (mul_pos hC (pow_pos (logWeight_pos _ _) _)) (h x hx hB)⟩

theorem hasLogGrowthEntries_inv (hG : IsLogBounded S w U G) :
    HasLogGrowthEntries S w U fun x => (G x)⁻¹ :=
  hG.inv.hasLogGrowthEntries

theorem of_trace (h0 : ∀ x ∈ U, x ∉ coordDivisor S w → (G x).PosDef)
    (h1 : HasLogGrowth S w U fun x => (G x).trace)
    (h2 : HasLogGrowth S w U fun x => (G x)⁻¹.trace) : IsLogBounded S w U G := by
  refine of_le (((HasLogGrowth.const (1 : ℝ)).add h1.norm).add h2.norm) fun x hx hB => ?_
  have hp : 0 < 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖ := by positivity
  have hG := h0 x hx hB
  let _ := hG.isUnit.invertible
  refine ⟨hp, ?_, (le_re_trace_smul_one_of_posSemidef hG.posSemidef).trans
    (real_smul_one_le_real_smul_one ?_)⟩
  · have h3 : (G x)⁻¹ ≤ (1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖) • (1 : Matrix n n ℂ) :=
      (le_re_trace_smul_one_of_posSemidef hG.inv.posSemidef).trans
        (real_smul_one_le_real_smul_one (by
          linarith [RCLike.re_le_norm (G x)⁻¹.trace, norm_nonneg (G x).trace]))
    have h4 := inv_le_inv_of_posDef_of_le hG.inv h3
    rwa [inv_real_smul_of_posDef PosDef.one hp.ne', inv_one, inv_inv_of_invertible] at h4
  · linarith [RCLike.re_le_norm (G x).trace, norm_nonneg (G x)⁻¹.trace]

end IsLogBounded

variable [Fintype n]

theorem isLogBounded_iff_entries : IsLogBounded S w U G ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → (G x).PosDef) ∧ HasLogGrowthEntries S w U G ∧
      HasLogGrowthEntries S w U fun x => (G x)⁻¹ :=
  ⟨fun h => ⟨fun _ => h.posDef, h.hasLogGrowthEntries, h.hasLogGrowthEntries_inv⟩,
    fun ⟨h0, h1, h2⟩ => .of_trace h0 h1.trace h2.trace⟩

theorem isLogBounded_iff_exists_scalar : IsLogBounded S w U G ↔
    ∃ g : X → ℝ, IsLogBoundedScalar S w U g ∧ ∀ x ∈ U, x ∉ coordDivisor S w →
      (g x)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧ G x ≤ g x • (1 : Matrix n n ℂ) := by
  refine ⟨fun h => ?_, fun ⟨g, hg, h⟩ =>
    .of_le hg.hasLogGrowth fun x hx hB => ⟨hg.pos hx hB, h x hx hB⟩⟩
  have hp : ∀ x, 1 ≤ 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖ := fun x => by
    linarith [norm_nonneg (G x).trace, norm_nonneg (G x)⁻¹.trace]
  refine ⟨fun x => 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖, isLogBoundedScalar_iff.2
    ⟨fun x _ _ => one_pos.trans_le (hp x), ((HasLogGrowth.const (1 : ℝ)).add
      h.hasLogGrowthEntries.trace.norm).add h.hasLogGrowthEntries_inv.trace.norm,
      (HasLogGrowth.const (1 : ℝ)).of_le fun x _ _ => ?_⟩, fun x hx hB => ?_⟩
  · rw [Real.norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans (hp x)))]
    exact inv_le_one_of_one_le₀ (hp x)
  have hG := h.posDef hx hB
  let _ := hG.isUnit.invertible
  refine ⟨?_, (le_re_trace_smul_one_of_posSemidef hG.posSemidef).trans
    (real_smul_one_le_real_smul_one ?_)⟩
  · have h3 : (G x)⁻¹ ≤ (1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖) • (1 : Matrix n n ℂ) :=
      (le_re_trace_smul_one_of_posSemidef hG.inv.posSemidef).trans
        (real_smul_one_le_real_smul_one (by
          linarith [RCLike.re_le_norm (G x)⁻¹.trace, norm_nonneg (G x).trace]))
    have h4 := inv_le_inv_of_posDef_of_le hG.inv h3
    rwa [inv_real_smul_of_posDef PosDef.one (one_pos.trans_le (hp x)).ne', inv_one,
      inv_inv_of_invertible] at h4
  · linarith [RCLike.re_le_norm (G x).trace, norm_nonneg (G x)⁻¹.trace]

theorem continuousOn_matrix_inv {A : X → Matrix n n ℂ} (hA : ContinuousOn A U)
    (hu : ∀ x ∈ U, IsUnit (A x)) : ContinuousOn (fun x => (A x)⁻¹) U := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((continuous_id.matrix_det.comp_continuousOn hA).inv₀ fun x hx =>
    ((isUnit_iff_isUnit_det _).1 (hu x hx)).ne_zero).smul
    (continuous_id.matrix_adjugate.comp_continuousOn hA)

namespace IsLogBounded

theorem of_continuousOn (hG : ContinuousOn G U) (h0 : ∀ x ∈ U, (G x).PosDef) :
    IsLogBounded S w U G :=
  isLogBounded_iff_entries.2 ⟨fun x hx _ => h0 x hx, .of_continuousOn hG,
    .of_continuousOn (continuousOn_matrix_inv hG fun x hx => (h0 x hx).isUnit)⟩

theorem of_le_of_le {G₁ G₂ : X → Matrix n n ℂ} (h₁ : IsLogBounded S w U G₁)
    (h₂ : IsLogBounded S w U G₂) (h : ∀ x ∈ U, x ∉ coordDivisor S w → G₁ x ≤ G x ∧ G x ≤ G₂ x) :
    IsLogBounded S w U G := by
  obtain ⟨g₁, hg₁, h₁⟩ := isLogBounded_iff_exists_scalar.1 h₁
  obtain ⟨g₂, hg₂, h₂⟩ := isLogBounded_iff_exists_scalar.1 h₂
  refine of_le (hg₁.hasLogGrowth.add hg₂.hasLogGrowth) fun x hx hB => ?_
  have p₁ := hg₁.pos hx hB
  have p₂ := hg₂.pos hx hB
  exact ⟨add_pos p₁ p₂,
    (real_smul_one_le_real_smul_one (inv_anti₀ p₁ (by linarith))).trans
      ((h₁ x hx hB).1.trans (h x hx hB).1),
    ((h x hx hB).2.trans (h₂ x hx hB).2).trans (real_smul_one_le_real_smul_one (by linarith))⟩

theorem smul {g : X → ℝ} (hg : IsLogBoundedScalar S w U g) (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => g x • G x :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => (hG.posDef hx hB).smul (hg.pos hx hB),
    fun i j => hg.hasLogGrowth.smul (hG.hasLogGrowthEntries i j),
    HasLogGrowthEntries.congr (A := fun x => (g x)⁻¹ • (G x)⁻¹)
      (fun i j => hg.hasLogGrowth_inv.smul (hG.hasLogGrowthEntries_inv i j))
      fun _ hx hB => inv_real_smul_of_posDef (hG.posDef hx hB) (hg.pos hx hB).ne'⟩

theorem smul_one {g : X → ℝ} (hg : IsLogBoundedScalar S w U g) :
    IsLogBounded S w U fun x => g x • (1 : Matrix n n ℂ) :=
  smul hg (of_continuousOn continuousOn_const fun _ _ => PosDef.one)

theorem diagonal {g : n → X → ℝ} (hg : ∀ i, IsLogBoundedScalar S w U (g i)) :
    IsLogBounded S w U fun x => Matrix.diagonal fun i => (g i x : ℂ) := by
  have key : ∀ {g : n → X → ℝ}, (∀ i, IsLogBoundedScalar S w U (g i)) →
      HasLogGrowthEntries S w U fun x => Matrix.diagonal fun i => (g i x : ℂ) := by
    intro g hg i j
    refine (hg i).hasLogGrowth.of_norm_le fun x _ _ => ?_
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [diagonal_apply_ne _ h]
  refine isLogBounded_iff_entries.2 ⟨fun x hx hB => PosDef.diagonal fun i => ?_, key hg,
    (key fun i => (hg i).inv).congr fun x hx hB => inv_eq_left_inv ?_⟩
  · exact_mod_cast (hg i).pos hx hB
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact_mod_cast inv_mul_cancel₀ ((hg i).pos hx hB).ne'

omit [Fintype n] in

theorem re_apply_self (hG : IsLogBounded S w U G) (i : n) :
    IsLogBoundedScalar S w U fun x => (G x i i).re := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ?_⟩
  have h' := h x hx hB
  generalize C * lwP₂ S (w x) ^ N = a at h' ⊢
  constructor
  · simpa using (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h'.1).diag_nonneg (i := i))).1
  · simpa using (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h'.2).diag_nonneg (i := i))).1

theorem re_det (hG : IsLogBounded S w U G) : IsLogBoundedScalar S w U fun x => (G x).det.re := by
  refine isLogBoundedScalar_iff.2 ⟨fun x hx hB => re_det_pos_of_posDef (hG.posDef hx hB),
    hG.hasLogGrowthEntries.det.of_norm_le fun x _ _ => Complex.abs_re_le_norm _,
    hG.hasLogGrowthEntries_inv.det.of_norm_le fun x hx hB => ?_⟩
  have h := Complex.re_eq_norm.2 (hG.posDef hx hB).det_pos.le
  rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, norm_inv, h, norm_norm]

theorem re_det_zpow (hG : IsLogBounded S w U G) (k : ℤ) :
    IsLogBoundedScalar S w U fun x => (G x).det.re ^ k :=
  hG.re_det.zpow k

end IsLogBounded

omit [Fintype n] in

theorem isLogBounded_of_unique_iff [Unique n] {g : X → ℝ} :
    (IsLogBounded S w U fun x => Matrix.of fun _ _ : n => (g x : ℂ)) ↔
      IsLogBoundedScalar S w U g := by
  refine ⟨fun h => by simpa using h.re_apply_self default, fun h => ?_⟩
  refine (IsLogBounded.smul_one h).congr fun x _ _ => ?_
  ext i j
  rw [Subsingleton.elim i j]
  simp

namespace IsLogBounded

theorem det_zpow (hG : IsLogBounded S w U G) (k : ℤ) (p : Type*) [Unique p] [DecidableEq p] :
    IsLogBounded S w U fun x => Matrix.of fun _ _ : p => (G x).det ^ k := by
  refine (isLogBounded_of_unique_iff.2 (hG.re_det_zpow k)).congr fun x hx hB => ?_
  have h : ((G x).det.re : ℂ) = (G x).det :=
    Complex.ext rfl (Complex.pos_iff.1 (hG.posDef hx hB).det_pos).2
  rw [Complex.ofReal_zpow, h]

theorem det (hG : IsLogBounded S w U G) (p : Type*) [Unique p] [DecidableEq p] :
    IsLogBounded S w U fun x => Matrix.of fun _ _ : p => (G x).det := by
  simpa using hG.det_zpow 1 p

theorem compoundMatrix {n : Type*} [Fintype n] [LinearOrder n] {G : X → Matrix n n ℂ}
    (hG : IsLogBounded S w U G) (k : ℕ) :
    IsLogBounded S w U fun x => compoundMatrix k (G x) :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => posDef_compoundMatrix k (hG.posDef hx hB),
    fun _ _ => (hG.hasLogGrowthEntries.submatrix _ _).det,
    HasLogGrowthEntries.congr (A := fun x => GlobalTheory.compoundMatrix k (G x)⁻¹)
      (fun _ _ => (hG.hasLogGrowthEntries_inv.submatrix _ _).det)
      fun _ hx hB => compoundMatrix_inv k (hG.posDef hx hB).isUnit⟩

theorem comp_of_logWeight (hG : IsLogBounded S w U G) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => lwP₂ S (w (π x))) :
    IsLogBounded S' w' U' fun x => G (π x) :=
  isLogBounded_iff_entries.2 ⟨fun x hx hx' => hG.posDef (hU hx) (hB x hx hx'),
    fun i j => (hG.hasLogGrowthEntries i j).comp_of_logWeight hπ hU hB hw,
    fun i j => (hG.hasLogGrowthEntries_inv i j).comp_of_logWeight hπ hU hB hw⟩

theorem comp (hG : IsLogBounded S w U G) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    IsLogBounded S' w' U' fun x => G (π x) :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => hG.posDef (hU hx) (hw.notMem hx hB),
    fun i j => (hG.hasLogGrowthEntries i j).comp hπ hU hw,
    fun i j => (hG.hasLogGrowthEntries_inv i j).comp hπ hU hw⟩

variable [Fintype m]

theorem conj_of_isLogBounded (hG : IsLogBounded S w U G) {A : X → Matrix n m ℂ}
    (hA : IsLogBounded S w U fun x => (A x)ᴴ * A x) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x := by
  obtain ⟨g, hg, h⟩ := isLogBounded_iff_exists_scalar.1 hG
  refine (hA.smul hg.inv).of_le_of_le (hA.smul hg) fun x hx hB => ⟨?_, ?_⟩
  · simpa using conjTranspose_mul_mul_le_of_le (h x hx hB).1 (A x)
  · simpa using conjTranspose_mul_mul_le_of_le (h x hx hB).2 (A x)

theorem conj_of_injective (hG : IsLogBounded S w U G) {A : X → Matrix n m ℂ}
    (hA : ContinuousOn A U) (hinj : ∀ x ∈ U, Function.Injective (A x).mulVec) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x :=
  hG.conj_of_isLogBounded (of_continuousOn
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).comp_continuousOn hA)
    fun x hx => PosDef.conjTranspose_mul_self _ (hinj x hx))

omit [Fintype m] [DecidableEq m] in

theorem conj (hG : IsLogBounded S w U G) {A : X → Matrix n n ℂ}
    (hA : ContinuousOn A U) (hu : ∀ x ∈ U, IsUnit (A x)) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x :=
  hG.conj_of_injective hA fun x hx => mulVec_injective_of_isUnit (hu x hx)

theorem fromBlocks (hH : IsLogBounded S w U H) (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => Matrix.fromBlocks (H x) 0 0 (G x) := by
  have key : ∀ {H : X → Matrix m m ℂ} {G : X → Matrix n n ℂ}, IsLogBounded S w U H →
      IsLogBounded S w U G →
        HasLogGrowthEntries S w U fun x => Matrix.fromBlocks (H x) 0 0 (G x) := by
    rintro H G hH hG (i | i) (j | j)
    exacts [hH.hasLogGrowthEntries i j, .const 0, .const 0, hG.hasLogGrowthEntries i j]
  refine isLogBounded_iff_entries.2 ⟨fun x hx hB =>
    posDef_fromBlocks_zero (hH.posDef hx hB) (hG.posDef hx hB), key hH hG,
    (key hH.inv hG.inv).congr fun x hx hB => inv_eq_left_inv ?_⟩
  let _ := (hH.posDef hx hB).isUnit.invertible
  let _ := (hG.posDef hx hB).isUnit.invertible
  simp [fromBlocks_multiply]

theorem schurComplement₁₁ {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => schurComplement₁₁ (G x) :=
  (hG.inv.submatrix Sum.inr_injective).inv.congr fun _ hx hB =>
    schurComplement₁₁_eq_inv (hG.posDef hx hB)

theorem schurComplement₂₂ {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => schurComplement₂₂ (G x) :=
  (hG.submatrix (e := Sum.swap) (Equiv.sumComm n m).injective).schurComplement₁₁

end IsLogBounded

end LogBounded

section Examples

example : lwP₂ (Finset.univ : Finset (Fin 2)) ![(Real.exp (-1) : ℝ), (Real.exp 2 : ℝ)] = 4 := by
  simp only [lwP₂, Fin.sum_univ_two, cons_val_zero, cons_val_one, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp, Real.log_exp]
  norm_num

example : schurComplement₁₁ (fromBlocks !![2] !![Complex.I] !![-Complex.I] !![1]) = !![1 / 2] := by
  ext i j
  fin_cases i; fin_cases j
  simp [schurComplement₁₁, Matrix.mul_apply, Matrix.inv_def]
  ring_nf
  simp
  norm_num

end Examples

end GlobalTheory
