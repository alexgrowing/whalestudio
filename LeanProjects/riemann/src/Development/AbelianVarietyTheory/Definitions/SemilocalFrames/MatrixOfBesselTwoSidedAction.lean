import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GG (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def opn {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g‖

def IsClosedSub (k r : ℕ) (S : Set (Mat k r)) : Prop :=
  S ⊆ GG k r ∧ IsClosed S ∧ (1 : Mat k r) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ ∀ a ∈ S, a⁻¹ ∈ S

def rmulM {k r : ℕ} (a : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * a

def invM {k r : ℕ} (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)

def IsUnimod {k r : ℕ} (S : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  (∀ s ∈ S, μ.map (rmulM s) = μ) ∧ μ.map invM = μ

def normInt {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (opn (Matrix.of x) ^ (-A)) ∂μ

def hPart (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j else if i = j then 1 else 0

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
variable {Wq : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def PiS (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  ψ ((hPart k r s)⁻¹ * s) • π (hPart k r s)

def coef (σ : Mat k r → (H →L[ℂ] H)) (u v : H) (g : Mat k r) : ℂ := ⟪v, σ g u⟫_ℂ

def SchurH (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g : Mt k r => coef σ v w (Matrix.of g) * star (coef σ v' w' (Matrix.of g))) μ ∧
    ∫ g, coef σ v w (Matrix.of g) * star (coef σ v' w' (Matrix.of g)) ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def DD (σ : Mat k r → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ g ∈ GG k r, v = σ g w}

def Decay (σ : Mat k r → (H →L[ℂ] H)) (V : Set H) (a : ℝ) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, ∃ C : ℝ, ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)

def Std (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) : Prop :=
  1 ≤ k ∧ IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ ∧ ‖w‖ = 1 ∧ IsHaarOn (GG k r) μG ∧ SchurH μG σ d ∧
    2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a ∧ Decay σ (DD σ w) a ∧ CompleteSpace H

def StdSm (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) : Prop :=
  Std σ w a μG d ∧ IsSmoothVec σ w

def Side (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ IsURepOn (UWset k r z) π ∧ IsHaarOn (Sset k r z) μS ∧
    FiniteDimensional ℂ Wp

def SideIrr (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) : Prop :=
  Side z π μS ∧ IsIrredOn (UWset k r z) π ∧ Nontrivial Wp

def be [CompleteSpace Wp] (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (u u' : H) : Wp →L[ℂ] Wp :=
  ∫ s, coef σ u u' (Matrix.of s) • PiS ψ π (Matrix.of s)⁻¹ ∂μS

def Afun [CompleteSpace Wp] (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (u v : H) (ξ : Wp) (x : Mat k r) : Wp :=
  be ψ π μS σ (σ x u) v ξ

def rk1 (a : Wp) (b : Wq) : Wq →L[ℂ] Wp := (innerSL ℂ b).smulRight a

def Greg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mat k r) :=
  {γ | γ ∈ GG k r ∧ (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' γ l ≠ 0) ∧ Gf k r z z' γ ≠ 0}

def act2 (γ : Mat k r) (p : Mt k r × Mt k r) : Mt k r := Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹

def IsDis (Ω : Set (Mat k r)) (μG μS μS' ν : Measure (Mt k r)) : Prop :=
  SigmaFinite ν ∧ ν {x | Matrix.of x ∉ Ω} = 0 ∧ ∀ f : Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ γ, (∫⁻ p, f (act2 (Matrix.of γ) p) ∂(μS.prod μS')) ∂ν

def orbNormInt (μS μS' : Measure (Mt k r)) (b : ℝ) (γ : Mat k r) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (opn (Matrix.of (act2 γ p)) ^ (-b)) ∂(μS.prod μS')

def Iint [CompleteSpace Wp] (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS μS' : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (x y : H)
    (ξ : Wp) (ξ' : Wq) (γ : Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, coef σ x y (Matrix.of (act2 γ p)) •
    rk1 (PiS ψ π (Matrix.of p.1)⁻¹ ξ) (PiS ψ' π' (Matrix.of p.2)⁻¹ ξ') ∂(μS.prod μS')

def OO [CompleteSpace Wp] (μ : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) :
    Wq →L[ℂ] Wp :=
  ∫ x, rk1 (Φ (Matrix.of x)) (Φ' (γ⁻¹ * Matrix.of x)) ∂μ

def IsFolner (S : Set (Mat k r)) (μ : Measure (Mt k r)) (Om : ℕ → Set (Mt k r)) : Prop :=
  (∀ j, MeasurableSet (Om j) ∧ (∀ x ∈ Om j, Matrix.of x ∈ S) ∧ Bornology.IsBounded (Om j) ∧
    0 < μ (Om j) ∧ μ (Om j) < ⊤) ∧
  ∀ C : Set (Mat k r), IsCompact C → C ⊆ S → ∃ Oc : ℕ → Set (Mt k r),
    (∀ j, MeasurableSet (Oc j) ∧ Oc j ⊆ Om j ∧ ∀ c ∈ C, ∀ x ∈ Oc j, lmulM c x ∈ Om j) ∧
    Filter.Tendsto (fun j => μ (Oc j) / μ (Om j)) Filter.atTop (nhds 1)

def MultOne (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Wp →L[ℂ] Wp)) : Prop :=
  ∀ B B' : H → Wp, IsBesselMapSm z ψ σ π B → IsBesselMapSm z ψ σ π B' →
    ∃ a : ℂ, (∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = a • B' x) ∨
      (∀ x ∈ smoothVecs (k := k) (r := r) σ, B' x = a • B x)

def NonVan [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Wp →L[ℂ] Wp)) (w : H) (μG ν : Measure (Mt k r)) : Prop :=
  ∃ W : Mat k r → Wp,
    AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    IsSPsiEquiv z ψ π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
    ∀ x ∈ GG k r, rconv μG (eFun μG σ w) W x = W x

def IsEll [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (μS : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (V : Set H) (l : H → Wp) : Prop :=
  IsBesselMapSm z ψ σ π l ∧ (∃ u ∈ V, l u ≠ 0) ∧ ∀ u ∈ V, ∀ u' ∈ V, be ψ π μS σ u u' = rk1 (l u) (l u')

def Vinf (σ : Mat k r → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (Ys : List (Mat k r)) (g : Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) ∧ g ∈ GG k r ∧
    v = dsigW σ Ys (σ g w)}

def dil (k r : ℕ) (τ : ℝ) : Mat k r := Matrix.diagonal fun i =>
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

theorem of_invM (x : Mt k r) : (Matrix.of (invM x) : Mat k r) = (Matrix.of x : Mat k r)⁻¹ := rfl

theorem invM_invM (x : Mt k r) (h : IsUnit (Matrix.of x : Mat k r).det) : invM (invM x) = x := by
  show ((((Matrix.of x : Mat k r)⁻¹ : Mat k r))⁻¹ : Mat k r) = Matrix.of x
  exact Matrix.nonsing_inv_nonsing_inv _ h

theorem measurable_invM : Measurable (invM : Mt k r → Mt k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := by exact continuous_id
  have hdet : Measurable fun x : Mt k r => ((Matrix.of x : Mat k r).det)⁻¹ :=
    hc.matrix_det.measurable.inv
  have hadj : ∀ i j, Measurable fun x : Mt k r => (Matrix.of x : Mat k r).adjugate i j :=
    fun i j => ((continuous_apply_apply i j).comp hc.matrix_adjugate).measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have key : (fun x : Mt k r => invM x i j) =
      fun x => ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    funext x
    simp [invM, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [key]
  exact hdet.mul (hadj i j)

theorem of_rmulM (a : Mat k r) (x : Mt k r) : (Matrix.of (rmulM a x) : Mat k r) = Matrix.of x * a := rfl

theorem continuous_rmulM (a : Mat k r) : Continuous (rmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => (continuous_apply_apply i l).mul continuous_const

theorem matrix_of_besselTwoSidedAction (γ : Mat k r) (p : Mt k r × Mt k r) :
    (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * Matrix.of (invM p.2) := rfl

theorem opn_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ opn g := norm_nonneg _

theorem opn_mul_le {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) : opn (g * h) ≤ opn g * opn h := by
  simp only [opn, map_mul]
  exact norm_mul_le _ _

theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  simp [opn]

theorem hPart_one : hPart k r 1 = 1 := by
  funext i j
  simp only [hPart]
  split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]

theorem PiS_one (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) : PiS ψ π 1 = ψ 1 • π 1 := by
  simp [PiS, hPart_one]

theorem coef_smul_left (σ : Mat k r → (H →L[ℂ] H)) (c : ℂ) (u v : H) (g : Mat k r) :
    coef σ (c • u) v g = c * coef σ u v g := by
  simp [coef]

theorem coef_smul_right (σ : Mat k r → (H →L[ℂ] H)) (c : ℂ) (u v : H) (g : Mat k r) :
    coef σ u (c • v) g = star c * coef σ u v g := by
  simp [coef, mul_comm]

theorem coef_add_left (σ : Mat k r → (H →L[ℂ] H)) (u u' v : H) (g : Mat k r) :
    coef σ (u + u') v g = coef σ u v g + coef σ u' v g := by
  simp [coef]

theorem coef_add_right (σ : Mat k r → (H →L[ℂ] H)) (u v v' : H) (g : Mat k r) :
    coef σ u (v + v') g = coef σ u v g + coef σ u v' g := by
  simp [coef]

theorem rankOneInnerOperator_apply (a : Wp) (b η : Wq) : rk1 a b η = ⟪b, η⟫_ℂ • a := rfl

theorem norm_rankOneInnerOperator (a : Wp) (b : Wq) : ‖rk1 a b‖ = ‖a‖ * ‖b‖ := by
  rw [rk1, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem mem_DD (σ : Mat k r → (H →L[ℂ] H)) (w : H) {g : Mat k r} (hg : g ∈ GG k r) : σ g w ∈ DD σ w := Submodule.subset_span ⟨g, hg, rfl⟩

theorem Decay.mono {σ : Mat k r → (H →L[ℂ] H)} {V V' : Set H} {a : ℝ} (h : Decay σ V a) (hV : V' ⊆ V) :
    Decay σ V' a := fun u hu v hv => h u (hV hu) v (hV hv)

theorem Greg_subset (z z' : Fin (2 * r + k + 1) → ℂ) : Greg k r z z' ⊆ GG k r := fun _ hγ => hγ.1

example : invM (k := 1) (r := 0) !![1, 2; 0, 1] = !![1, -2; 0, 1] := by
  show ((!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = _
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

example (x : Mt k r) : invM x = @Inv.inv (Mat k r) Matrix.inv (Matrix.of x) := rfl

example : dil 1 1 2 = Matrix.diagonal ![2, 1, 1, 2⁻¹] := by
  unfold dil
  congr 1; funext i
  fin_cases i <;> simp

example : rk1 (1 : ℂ) (Complex.I : ℂ) (1 : ℂ) = -Complex.I := by simp [rankOneInnerOperator_apply]

end GlobalTheory.SgInf
