import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockModelA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}

def prodSpan (L : Submodule (𝓞 K) (Fin m → K)) (d : ℕ) : Submodule (𝓞 K) (MvPolynomial (Fin m) K) :=
  Submodule.span (𝓞 K) {p | ∃ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) ∧ p = ∏ i, latticeForm (u i)}

theorem one_mem_prodSpan_zero : (1 : MvPolynomial (Fin m) K) ∈ prodSpan L 0 :=
  Submodule.subset_span ⟨Fin.elim0, fun i ↦ i.elim0, by simp⟩

theorem latticeForm_mem_prodSpan_one {u : Fin m → K} (hu : u ∈ latticeDual L) :
    latticeForm u ∈ prodSpan L 1 :=
  Submodule.subset_span ⟨fun _ ↦ u, fun _ ↦ hu, by simp⟩

theorem mul_mem_prodSpan {a b : ℕ} {p q : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L a)
    (hq : q ∈ prodSpan L b) : p * q ∈ prodSpan L (a + b) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨Fin.append u v, fun i ↦ ?_, ?_⟩
      · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
        · rw [Fin.append_left]; exact hu i
        · rw [Fin.append_right]; exact hv i
      · rw [Fin.prod_univ_add]
        simp [Fin.append_left, Fin.append_right]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [← algebraMap_smul K c y, smul_eq_C_mul, mul_left_comm, ← smul_eq_C_mul, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul K c x, smul_eq_C_mul, mul_assoc, ← smul_eq_C_mul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem pow_mem_prodSpan {p : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L 1) (k : ℕ) :
    p ^ k ∈ prodSpan L k := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_prodSpan_zero
  | succ k ih => rw [pow_succ]; exact mul_mem_prodSpan ih hp

theorem prod_mem_prodSpan {ι : Type*} (t : Finset ι) (g : ι → MvPolynomial (Fin m) K) (e : ι → ℕ)
    (h : ∀ i ∈ t, g i ∈ prodSpan L (e i)) : ∏ i ∈ t, g i ∈ prodSpan L (∑ i ∈ t, e i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_mem_prodSpan_zero
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_prodSpan (h i (Finset.mem_insert_self i t))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem smul_mem_dual (c : 𝓞 K) {u : Fin m → K} (hu : u ∈ latticeDual L) :
    algebraMap (𝓞 K) K c • u ∈ latticeDual L := by
  intro v hv
  obtain ⟨b, hb⟩ := hu v hv
  exact ⟨c * b, by rw [map_mul, hb, smul_dotProduct, smul_eq_mul]⟩

variable {φ : Fin (N + 1) → Fin m → K}

theorem latticeMap_mem_prodSpan (hφ : IsDualBasis L φ) {d : ℕ}
    {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ} (hf : f.IsHomogeneous d) : latticeMap φ f ∈ prodSpan L d := by
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hdeg : s.degree = d := by
    have := hf (mem_support_iff.mp hs)
    rwa [weight_one_eq_degree] at this
  rw [latticeMap, coe_eval₂Hom, eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
  refine zsmul_mem ?_ _
  rw [← hdeg, Finsupp.prod, Finsupp.degree]
  exact prod_mem_prodSpan _ _ _ fun v _ ↦ pow_mem_prodSpan (latticeForm_mem_prodSpan_one (mem_dual hφ v.2)) _

theorem prod_mem_latticeMap_image (hφ : IsDualBasis L φ) {d : ℕ} (u : Fin d → Fin m → K)
    (hu : ∀ i, u i ∈ latticeDual L) :
    ∃ f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, f.IsHomogeneous d ∧ latticeMap φ f = ∏ i, latticeForm (u i) := by
  choose c hc using fun i ↦ (mem_dual_iff hφ (u i)).mp (hu i)
  refine ⟨∏ i, ∑ b, C (c i b) * X ⟨(), b⟩, ?_, ?_⟩
  · have h := IsHomogeneous.prod Finset.univ (fun i ↦ ∑ b, C (c i b) * X (⟨(), b⟩ : Coord fun _ : Unit ↦ N))
      (fun _ ↦ 1) fun i _ ↦ IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _
    simpa using h
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [latticeMap_linear, hc i]

theorem latticeMap_image_homogeneous (hφ : IsDualBasis L φ) {d : ℕ} (hd : 1 ≤ d) :
    latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)} =
      (prodSpan L d : Set (MvPolynomial (Fin m) K)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact latticeMap_mem_prodSpan hφ ((isWeightedHomogeneous_coordDeg_iff f _).mp hf)
  · intro p hp
    set Img := latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)}
    have hadd : ∀ x ∈ Img, ∀ y ∈ Img, x + y ∈ Img := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      exact ⟨f + g, hf.add hg, map_add _ _ _⟩
    have hprod : ∀ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) → ∏ i, latticeForm (u i) ∈ Img := by
      intro u hu
      obtain ⟨f, hf, hfu⟩ := prod_mem_latticeMap_image hφ u hu
      exact ⟨f, (isWeightedHomogeneous_coordDeg_iff f _).mpr hf, hfu⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have key : ∀ x ∈ prodSpan L (k + 1), ∀ c : 𝓞 K, C (algebraMap (𝓞 K) K c) * x ∈ Img := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        intro c
        have hc : C (algebraMap (𝓞 K) K c) * ∏ i, latticeForm (u i) =
            ∏ i, latticeForm ((Fin.cons (algebraMap (𝓞 K) K c • u 0) (Fin.tail u) : Fin (k + 1) → Fin m → K) i) := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, ← mul_assoc, latticeForm_smul]
          rfl
        rw [hc]
        refine hprod _ fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
        · rw [Fin.cons_zero]; exact smul_mem_dual c (hu 0)
        · rw [Fin.cons_succ]; exact hu j.succ
      | zero =>
        intro c
        exact ⟨0, isWeightedHomogeneous_zero _ _ _, by rw [mul_zero, map_zero]⟩
      | add x y _ _ hx hy =>
        intro c
        rw [mul_add]
        exact hadd _ (hx c) _ (hy c)
      | smul a x _ hx =>
        intro c
        rw [← algebraMap_smul K a x, smul_eq_C_mul, ← mul_assoc, ← map_mul, ← map_mul]
        exact hx (c * a)
    simpa using key p hp 1

section Birational

variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}

def yEval (φ : Fin (N + 1) → Fin (r + 1) → K) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* LatticeField K r :=
  eval₂Hom (Int.castRingHom _) (latticeCoord φ)

theorem yEval_eq (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) : yEval φ g = dehom K r (latticeMap φ g) := by
  have h : yEval φ = (dehom K r).comp (latticeMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [yEval, latticeMap]
    · intro v
      simp [yEval, latticeMap, latticeCoord_eq]
  rw [h, RingHom.comp_apply]

theorem dehom_latticeForm_apply (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = ∑ j, algebraMap K (LatticeField K r) (u j) * genericVal K r j := by
  simp [dehom, latticeForm]

theorem dehom_latticeForm_ne_zero {u : Fin (r + 1) → K} (hu : u ≠ 0) : dehom K r (latticeForm u) ≠ 0 := by
  rw [dehom_latticeForm]
  intro h
  apply hu
  have h' := IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r) (h.trans (map_zero _).symm)
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have := congrArg (coeff 0) h'
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C] using this
  · have := congrArg (coeff (Finsupp.single i 1)) h'
    have h0 : (0 : Fin r →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C, Finsupp.single_left_inj, h0] using this

theorem dehom_single_zero : dehom K r (latticeForm (Pi.single 0 1 : Fin (r + 1) → K)) = 1 := by
  simp [dehom, latticeForm, Pi.single_apply, genericVal]

theorem yEval_C_mul (k : ℤ) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    yEval φ (C k * g) = k * yEval φ g := by
  rw [yEval, coe_eval₂Hom, eval₂_mul, eval₂_C, eq_intCast]

theorem dehom_latticeForm_intSmul (k : ℤ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm ((k : K) • u)) = k * dehom K r (latticeForm u) := by
  rw [latticeForm_smul, map_mul]
  simp [dehom]

theorem exists_linear_of_mem {m : ℕ} {L' : Submodule (𝓞 K) (Fin m → K)} {φ' : Fin (N + 1) → Fin m → K}
    (hφ : IsDualBasis L' φ') {u : Fin m → K} (hu : u ∈ latticeDual L') :
    ∃ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, g.IsHomogeneous 1 ∧ latticeMap φ' g = latticeForm u := by
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ u).mp hu
  exact ⟨∑ b, C (c b) * X ⟨(), b⟩, IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _,
    by rw [latticeMap_linear, hc]⟩

def quotField (φ : Fin (N + 1) → Fin (r + 1) → K) : Subfield (LatticeField K r) where
  carrier := {s | ∃ (d : ℕ) (g h : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ), g.IsHomogeneous d ∧ h.IsHomogeneous d ∧
    yEval φ h ≠ 0 ∧ yEval φ g = s * yEval φ h}
  mul_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    exact ⟨d + d', g * g', h * h', hg.mul hg', hh.mul hh', by rw [map_mul]; exact mul_ne_zero hne hne',
      by rw [map_mul, map_mul, he, he']; ring⟩
  one_mem' := ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  add_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    refine ⟨d + d', g * h' + h * g', h * h', (hg.mul hh').add (hh.mul hg'), hh.mul hh',
      by rw [map_mul]; exact mul_ne_zero hne hne', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, he, he']
    ring
  zero_mem' := ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    exact ⟨d, -g, h, hg.neg, hh, hne, by rw [map_neg, he]; ring⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    by_cases hs : s = 0
    · subst hs
      rw [inv_zero]
      exact ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hs hne, ?_⟩
      rw [he]
      field_simp

theorem dehom_mem_quotField (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) ∈ quotField φ := by
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨n', hn', hne⟩ := exists_int_smul_mem_latticeDual hL (Pi.single 0 1 : Fin (r + 1) → K)
  obtain ⟨g, hg, hgu⟩ := exists_linear_of_mem (N := N) hφ hnu
  obtain ⟨h, hh, hhe⟩ := exists_linear_of_mem (N := N) hφ hne
  have hg' : yEval φ g = n * dehom K r (latticeForm u) := by
    rw [yEval_eq, hgu, dehom_latticeForm_intSmul]
  have hh' : yEval φ h = n' := by
    rw [yEval_eq, hhe, dehom_latticeForm_intSmul, dehom_single_zero, mul_one]
  refine ⟨1, C n' * g, C n * h, by simpa using (isHomogeneous_C _ _).mul hg,
    by simpa using (isHomogeneous_C _ _).mul hh, ?_, ?_⟩
  · rw [yEval_C_mul, hh']
    exact mul_ne_zero (Int.cast_ne_zero.mpr hn) (Int.cast_ne_zero.mpr hn')
  · rw [yEval_C_mul, yEval_C_mul, hg', hh']
    ring

theorem mem_quotField (hL : L.FG) (hφ : IsDualBasis L φ) (s : LatticeField K r) : s ∈ quotField φ := by
  have hpoly : ∀ p : MvPolynomial (Fin r) K, algebraMap _ (LatticeField K r) p ∈ quotField φ := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = dehom K r (latticeForm (Pi.single 0 a)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal, algebraMap_C, Fin.sum_univ_succ]
      rw [e]
      exact dehom_mem_quotField hL hφ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j) = dehom K r (latticeForm (Pi.single j.succ 1)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal]
      rw [e]
      exact dehom_mem_quotField hL hφ _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin r) K) s
  exact div_mem (hpoly a) (hpoly b)

theorem isMultiHomog_iff (g : Geo.MRing (blockIdx fun _ : Unit ↦ N)) (d : Unit → ℕ) :
    Geo.IsMultiHomog g d ↔ g.IsHomogeneous (d ()) := by
  have hdeg : ∀ s : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ, ∑ i : Fin (N + 1), s ⟨(), i⟩ = s.degree := by
    intro s
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  constructor
  · intro h s hs
    rw [weight_one_eq_degree, ← hdeg]
    exact h s (mem_support_iff.mpr hs) ()
  · intro h s hs k
    have := h (mem_support_iff.mp hs)
    rw [weight_one_eq_degree, ← hdeg] at this
    exact this

theorem birational_latticeCoord (hL : L.FG) (hφ : IsDualBasis L φ) :
    Geo.Birational (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, he⟩ := mem_quotField hL hφ s
  refine ⟨fun _ ↦ d, g, h, (isMultiHomog_iff g _).mpr hg, (isMultiHomog_iff h _).mpr hh, ?_, ?_⟩
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using hne
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using he

end Birational

end LatticeModel

end

end GroundTheory.Heights₂.Heights
