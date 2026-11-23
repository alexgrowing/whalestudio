import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K]

theorem isAlgebraic_int (x : K) : IsAlgebraic ℤ x :=
  IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)

theorem exists_int_mul_integral (x : K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = n * x := by
  obtain ⟨n, s, hn, h⟩ := (isAlgebraic_int x).exists_smul_eq (𝓞 K)
  exact ⟨n, hn, s, by rw [← h, zsmul_eq_mul]⟩

theorem exists_int_smul_mem_latticeDual {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG)
    (u : Fin m → K) : ∃ n : ℤ, n ≠ 0 ∧ (n : K) • u ∈ latticeDual L := by
  classical
  obtain ⟨s, rfl⟩ := hL
  choose n hn a ha using fun g : Fin m → K ↦ exists_int_mul_integral (u ⬝ᵥ g)
  refine ⟨∏ g ∈ s, n g, Finset.prod_ne_zero_iff.mpr fun g _ ↦ hn g, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨((∏ g ∈ s.erase x, n g : ℤ) : 𝓞 K) * a x, ?_⟩
    rw [map_mul, map_intCast, ha x, smul_dotProduct, smul_eq_mul, ← Finset.mul_prod_erase s n hx]
    push_cast
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨b + c, by rw [map_add, hb, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨c * b, by rw [map_mul, hb, dotProduct_smul, Algebra.smul_def c]⟩

variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}

theorem mem_dual_iff (hφ : IsDualBasis L φ) (u : Fin m → K) :
    u ∈ latticeDual L ↔ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = u := by
  rw [← Submodule.mem_span_range_iff_exists_fun ℤ, hφ.span_eq, Submodule.restrictScalars_mem]

theorem mem_dual (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : φ b ∈ latticeDual L :=
  (mem_dual_iff hφ _).mpr ⟨Pi.single b 1, by simp [Pi.single_apply]⟩

theorem latticeForm_add (u v : Fin m → K) : latticeForm (u + v) = latticeForm u + latticeForm v := by
  simp [latticeForm, add_mul, Finset.sum_add_distrib]

theorem latticeForm_smul (c : K) (u : Fin m → K) : latticeForm (c • u) = C c * latticeForm u := by
  simp [latticeForm, Finset.mul_sum, mul_assoc]

theorem latticeForm_zero : latticeForm (0 : Fin m → K) = 0 := by
  simp [latticeForm]

theorem latticeForm_zsmul (c : ℤ) (u : Fin m → K) : latticeForm (c • u) = C (c : K) * latticeForm u := by
  rw [← latticeForm_smul]
  congr 1
  ext j
  simp

theorem latticeForm_sum {ι : Type*} (s : Finset ι) (u : ι → Fin m → K) :
    latticeForm (∑ i ∈ s, u i) = ∑ i ∈ s, latticeForm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [latticeForm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, latticeForm_add, ih]

theorem coeff_latticeForm (u : Fin m → K) (j : Fin m) :
    coeff (Finsupp.single j 1) (latticeForm u) = u j := by
  simp [latticeForm, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem latticeForm_eq_zero_iff (u : Fin m → K) : latticeForm u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ h ▸ latticeForm_zero⟩
  rw [← coeff_latticeForm u j, h, coeff_zero, Pi.zero_apply]

theorem isHomogeneous_latticeForm (u : Fin m → K) : (latticeForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

theorem latticeMap_linear (φ : Fin (N + 1) → Fin m → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, C (c b) * X ⟨(), b⟩) = latticeForm (∑ b, c b • φ b) := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul]
  simp [latticeMap]

theorem isHomogeneous_latticeMap (φ : Fin (N + 1) → Fin m → K) {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ}
    {d : ℕ} (hf : f.IsHomogeneous d) : (latticeMap φ f).IsHomogeneous d := by
  have h := hf.eval₂ (Int.castRingHom _) (fun v ↦ latticeForm (φ v.2))
    (fun a ↦ by rw [eq_intCast, ← map_intCast (C : K →+* MvPolynomial (Fin m) K)]; exact isHomogeneous_C _ _)
    (fun v ↦ isHomogeneous_latticeForm _)
  rwa [one_mul] at h

section Degrees

variable {R : Type*} [CommSemiring R]

theorem weight_coordDeg (s : Coord (fun _ : Unit ↦ N) →₀ ℕ) :
    Finsupp.weight (coordDeg fun _ : Unit ↦ N) s = fun _ ↦ s.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.degree]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp [coordDeg]

theorem weight_one_eq_degree {σ : Type*} (s : σ →₀ ℕ) : Finsupp.weight (1 : σ → ℕ) s = s.degree := by
  rw [Finsupp.degree_eq_weight_one]
  rfl

theorem isWeightedHomogeneous_coordDeg_iff (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f μ ↔ f.IsHomogeneous (μ ()) := by
  constructor
  · intro h s hs
    have := congrFun (h hs) ()
    rw [weight_coordDeg] at this
    rw [weight_one_eq_degree]
    exact this
  · intro h s hs
    rw [weight_coordDeg]
    funext u
    have := h hs
    rw [weight_one_eq_degree] at this
    exact this

theorem weightedHomogeneousComponent_coordDeg (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ N) μ f = homogeneousComponent (μ ()) f := by
  classical
  ext s
  rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_coordDeg]
  by_cases h : s.degree = μ ()
  · rw [if_pos (funext fun _ ↦ h), if_pos h]
  · rw [if_neg (fun h' ↦ h (congrFun h' ())), if_neg h]

end Degrees

theorem latticeMap_homogeneousComponent (φ : Fin (N + 1) → Fin m → K)
    (f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) (d : ℕ) :
    latticeMap φ (homogeneousComponent d f) = homogeneousComponent d (latticeMap φ f) := by
  classical
  conv_rhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem (isHomogeneous_latticeMap φ (homogeneousComponent_isHomogeneous _ f))]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

def latticeVariety (φ : Fin (N + 1) → Fin m → K) (hφ : IsDualBasis L φ) :
    ArithVariety (fun _ : Unit ↦ N) where
  ideal := latticeIdeal φ
  isPrime := RingHom.ker_isPrime _
  homogeneous f hf μ := by
    rw [weightedHomogeneousComponent_coordDeg]
    refine RingHom.mem_ker.mpr ?_
    rw [latticeMap_homogeneousComponent, RingHom.mem_ker.mp hf, map_zero]
  relevant _ := ⟨0, fun h ↦ hφ.independent.ne_zero 0
    ((latticeForm_eq_zero_iff _).mp (by simpa [latticeMap] using RingHom.mem_ker.mp h))⟩
  horizontal a ha := by simpa [latticeMap] using RingHom.mem_ker.mp ha

theorem latticeVariety_ideal (φ : Fin (N + 1) → Fin m → K) (hφ : IsDualBasis L φ) :
    (latticeVariety φ hφ).ideal = latticeIdeal φ := rfl

variable {r : ℕ}

theorem algebraMap_C (a : K) :
    algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = algebraMap K (LatticeField K r) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin r) K) (LatticeField K r), MvPolynomial.algebraMap_eq]

def genericVal (K : Type) [Field K] (r : ℕ) : Fin (r + 1) → LatticeField K r :=
  Fin.cases 1 fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)

def dehom (K : Type) [Field K] (r : ℕ) : MvPolynomial (Fin (r + 1)) K →+* LatticeField K r :=
  eval₂Hom (algebraMap K (LatticeField K r)) (genericVal K r)

theorem dehom_latticeForm (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
      (C (u 0) + ∑ j : Fin r, C (u j.succ) * X j) := by
  simp only [dehom, latticeForm, map_sum, map_mul, map_add, coe_eval₂Hom, eval₂_C, eval₂_X, algebraMap_C,
    Fin.sum_univ_succ, genericVal, Fin.cases_zero, Fin.cases_succ, mul_one]

theorem latticeCoord_eq (φ : Fin (N + 1) → Fin (r + 1) → K) (v : Coord fun _ : Unit ↦ N) :
    latticeCoord φ v = dehom K r (latticeForm (φ v.2)) :=
  (dehom_latticeForm _).symm

theorem aeval_latticeCoord (φ : Fin (N + 1) → Fin (r + 1) → K) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    aeval (latticeCoord φ) g = dehom K r (latticeMap φ g) := by
  have h : (aeval (latticeCoord φ)).toRingHom = (dehom K r).comp (latticeMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [latticeMap]
    · intro v
      simp [latticeMap, latticeCoord_eq]
  exact RingHom.congr_fun h g

theorem mCoordIdeal_latticeCoord (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) = latticeIdeal φ := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, latticeIdeal, RingHom.mem_ker]
  constructor
  · intro hf
    have hw : ∀ w : Fin (r + 1) → K, w 0 ≠ 0 → eval w (latticeMap φ f) = 0 := by
      intro w hw0
      let χ : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* MvPolynomial (Fin r) K :=
        eval₂Hom (Int.castRingHom _) fun v ↦ C (w 0) * (C (φ v.2 0) + ∑ j : Fin r, C (φ v.2 j.succ) * X j)
      have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun _ : Unit ↦ algebraMap K (LatticeField K r) (w 0))
            (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g) =
          algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (χ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [Geo.mConeMap, χ]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [Geo.mConeMap, aeval_X, map_mul, eval_C, eval_X, χ, coe_eval₂Hom, eval₂_X, algebraMap_C,
            latticeCoord]
          ring
      have h2 : χ f = 0 := by
        apply IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r)
        rw [map_zero, ← h1, hf, map_zero]
      have h3 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun j : Fin r ↦ w j.succ / w 0) (χ g) = eval w (latticeMap φ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [χ, latticeMap]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [χ, latticeMap, coe_eval₂Hom, eval₂_X, latticeForm, map_mul, map_add, map_sum, eval_C, eval_X,
            Fin.sum_univ_succ]
          rw [mul_add, Finset.mul_sum]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro j _
            field_simp
      rw [← h3, h2, map_zero]
    have hX : (X 0 : MvPolynomial (Fin (r + 1)) K) * latticeMap φ f = 0 := by
      apply MvPolynomial.funext
      intro w
      by_cases h0 : w 0 = 0
      · simp [h0]
      · simp [hw w h0]
    exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)
  · intro hf
    let ψ : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial Unit (LatticeField K r) :=
      eval₂Hom (C.comp (algebraMap K (LatticeField K r))) fun j ↦ C (genericVal K r j) * X ()
    have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
        Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g = ψ (latticeMap φ g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [Geo.mConeMap, ψ, latticeMap]
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
      | mul_X p v hp =>
        rw [map_mul, map_mul, hp, map_mul]
        congr 1
        obtain ⟨⟨⟩, b⟩ := v
        simp only [Geo.mConeMap, aeval_X, latticeCoord_eq, dehom, latticeMap, ψ, coe_eval₂Hom, eval₂_X,
          latticeForm, map_sum, map_mul, eval₂_C, RingHom.comp_apply, Finset.sum_mul, mul_assoc]
    rw [h1, hf, map_zero]

end LatticeModel

end

end GroundTheory.Heights₂.Heights
