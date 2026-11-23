import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IwaInt

variable {n : ℕ}

def crd (p : Fin n × Fin n × Bool → Prop) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ({t // p t} → ℝ) where
  toFun x t := if t.1.2.2 then (x t.1.1 t.1.2.1).im else (x t.1.1 t.1.2.1).re
  map_add' x y := by
    funext t; by_cases h : t.1.2.2 <;> simp [h]
  map_smul' a x := by
    funext t; by_cases h : t.1.2.2 <;> simp [h]

def emb (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] :
    ({t // p t} → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := Matrix.of fun i j =>
    ⟨if h : p (i, j, false) then v ⟨_, h⟩ else 0, if h : p (i, j, true) then v ⟨_, h⟩ else 0⟩
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp <;> split_ifs <;> simp
  map_smul' a x := by
    ext i j
    apply Complex.ext <;> simp

def Lc (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    ({t // p t} → ℝ) →ₗ[ℝ] ({t // p t} → ℝ) :=
  crd p ∘ₗ LinearMap.mulLeft ℝ x ∘ₗ emb p

def Rc (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    ({t // p t} → ℝ) →ₗ[ℝ] ({t // p t} → ℝ) :=
  crd p ∘ₗ LinearMap.mulRight ℝ x ∘ₗ emb p

abbrev pV (ε : Fin n → Bool) (t : Fin n × Fin n × Bool) : Prop := ε t.1 = ε t.2.1

abbrev pW (ε : Fin n → Bool) (t : Fin n × Fin n × Bool) : Prop :=
  ε t.1 = ε t.2.1 ∧ (t.2.1 < t.1 ∨ (t.1 = t.2.1 ∧ t.2.2 = false))

lemma crd_emb (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (v : {t // p t} → ℝ) :
    crd p (emb p v) = v := by
  funext ⟨⟨i, j, s⟩, h⟩
  cases s <;> simp [crd, emb, h]

lemma emb_crd_iff (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (x : Matrix (Fin n) (Fin n) ℂ) :
    emb p (crd p x) = x ↔ ∀ i j, (¬ p (i, j, false) → (x i j).re = 0) ∧ (¬ p (i, j, true) → (x i j).im = 0) := by
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    constructor
    · intro hp
      rw [← h1]; simp [emb, hp]
    · intro hp
      rw [← h1]; simp [emb, hp]
  · intro h
    ext i j
    apply Complex.ext
    · by_cases hp : p (i, j, false)
      · simp [emb, crd, hp]
      · simp [emb, hp, (h i j).1 hp]
    · by_cases hp : p (i, j, true)
      · simp [emb, crd, hp]
      · simp [emb, hp, (h i j).2 hp]

lemma comm_J_iff (ε : Fin n → Bool) (x : Matrix (Fin n) (Fin n) ℂ) :
    x * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * x ↔ ∀ i j, ε i ≠ ε j → x i j = 0 := by
  unfold Formalism.REAL.Jm
  constructor
  · intro h i j hij
    have h1 := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    cases hi : ε i <;> cases hj : ε j <;> simp [hi, hj] at h1 hij
    · linear_combination (1 / 2 : ℂ) * h1
    · linear_combination (-1 / 2 : ℂ) * h1
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : ε i = ε j
    · rw [hij, mul_comm]
    · rw [h i j hij]; simp

lemma isLo_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) : IsLo (a * b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [ha i k hk, zero_mul]
  · rw [hb k j (lt_of_le_of_lt (not_lt.1 hk) hij), mul_zero]

lemma isLo_mul_diag {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) (i : Fin n) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hb k i h, mul_zero]
  · rw [ha i k h, zero_mul]

lemma isLo_inv {a : (Matrix (Fin n) (Fin n) ℂ)ˣ} (ha : IsLo (a : Matrix (Fin n) (Fin n) ℂ)) :
    IsLo ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hb : Matrix.BlockTriangular (a : Matrix (Fin n) (Fin n) ℂ) (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
    fun i j h => ha i j h
  letI : Invertible (a : Matrix (Fin n) (Fin n) ℂ) := a.invertible
  have h2 := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [Matrix.coe_units_inv]
  exact fun i j h => h2 h

def GC (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g}
  mul_mem' := by
    intro g h hg hh
    have hg' : Commute (g : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hg
    have hh' : Commute (h : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hh
    exact hg'.mul_left hh'
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    have hg' : Commute (g : Matrix (Fin n) (Fin n) ℂ) (Formalism.REAL.Jm ε) := hg
    exact hg'.units_inv_left

def BC (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | g ∈ GC ε ∧ IsLo (g : Matrix (Fin n) (Fin n) ℂ) ∧ ∀ l, 0 < (g : Matrix (Fin n) (Fin n) ℂ) l l}
  mul_mem' := by
    intro g h hg hh
    refine ⟨mul_mem hg.1 hh.1, isLo_mul hg.2.1 hh.2.1, fun l => ?_⟩
    rw [Units.val_mul, isLo_mul_diag hg.2.1 hh.2.1]
    exact mul_pos (hg.2.2 l) (hh.2.2 l)
  one_mem' := ⟨one_mem _, fun i j h => by simp [Matrix.one_apply, h.ne], fun l => by simp⟩
  inv_mem' := by
    intro g hg
    refine ⟨inv_mem hg.1, isLo_inv hg.2.1, fun l => ?_⟩
    have h1 := isLo_mul_diag hg.2.1 (isLo_inv hg.2.1) l
    rw [Units.mul_inv, Matrix.one_apply_eq] at h1
    rw [← inv_eq_of_mul_eq_one_right h1.symm]
    exact inv_pos.2 (hg.2.2 l)

lemma isEmbedding_val : Topology.IsEmbedding
    (Units.val : (Matrix (Fin n) (Fin n) ℂ)ˣ → Matrix (Fin n) (Fin n) ℂ) := by
  refine Units.isEmbedding_val_mk' (f := fun x => x⁻¹) ?_ (fun u => (Matrix.coe_units_inv u).symm)
  intro x hx
  refine (continuousAt_matrix_inv x ?_).continuousWithinAt
  have h : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
  have := NormedRing.inverse_continuousAt (Units.mk0 _ h)
  simpa using this

instance instSecondCountableSub (Γ : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : SecondCountableTopology Γ := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isEmbedding_val.comp Topology.IsEmbedding.subtypeVal).isInducing.secondCountableTopology

instance instMeasGC (ε : Fin n → Bool) : MeasurableSpace (GC ε) := borel _
instance instBorelGC (ε : Fin n → Bool) : BorelSpace (GC ε) := ⟨rfl⟩
instance instMeasBC (ε : Fin n → Bool) : MeasurableSpace (BC ε) := borel _
instance instBorelBC (ε : Fin n → Bool) : BorelSpace (BC ε) := ⟨rfl⟩

end GlobalTheory.IwaInt
