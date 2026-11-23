import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def sgnCN (k r : ℕ) : Fin (2 * r + k + 1) → Bool := fun i =>
  if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def IsShape (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (bv : ℝ) : Prop :=
  IsHCParam lam ∧ (∀ i, i.val < k - 1 → 0 ≤ lam i ∧ lam i ≤ bv / 8) ∧
    ∀ i, k - 1 ≤ i.val → -(2 * bv) ≤ lam i ∧ lam i ≤ -bv

def IsRange (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c h q : ℝ) : Prop :=
  0 < c ∧ GapAtLeast (sgnCN k r) lam h ∧ 100 * max 1 c * q * Real.sqrt (2 * r + 2) ≤ c * h ∧
    ∀ i j : Fin (2 * r + k + 1), i < j → j.val < k - 1 → 100 * max 1 c * q ≤ lam i - lam j

def dist1 {n : ℕ} (μ lam : Fin n → ℝ) : ℝ := ∑ a, |μ a - lam a|

def InPP {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) (μ : Fin n → ℝ) : Prop :=
  (∀ a, ∃ m : ℤ, μ a - lam a = (m : ℝ)) ∧ dist1 μ lam ≤ t

structure HRep (k r : ℕ) where
  H : Type
  [nG : NormedAddCommGroup H]
  [iP : InnerProductSpace ℂ H]
  σ : Mat k r → (H →L[ℂ] H)

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

def HRep.onJ (A : HRep k r) (P : Mat k r) : Mat k r → (A.H →L[ℂ] A.H) := fun g => A.σ (P⁻¹ * g * P)

def HRep.IsDSAt (A : HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) : Prop :=
  IsDS (sgnCN k r) μ (A.onJ P)

def HRep.gl (A : HRep k r) (X : Mat k r) (v : A.H) : A.H :=
  dsig A.σ ((1 / 2 : ℂ) • (X - Hpk k r * Xᴴ * Hpk k r)) v +
    Complex.I • dsig A.σ ((-Complex.I / 2) • (X + Hpk k r * Xᴴ * Hpk k r)) v

def HRep.E (A : HRep k r) (P : Mat k r) (a b : Fin (2 * r + k + 1)) (v : A.H) : A.H :=
  A.gl (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v

def HRep.Ew (A : HRep k r) (P : Mat k r) (w : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (v : A.H) : A.H :=
  w.foldr (fun e x => A.E P e.1 e.2 x) v

def HRep.iso (A : HRep k r) (P : Mat k r) (ν : Fin (2 * r + k + 1) → ℝ) : Submodule ℂ A.H :=
  sSup {S | IsKTypeOf (sgnCN k r) (A.onJ P) ν S}

def HRep.filt (A : HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) (j : ℕ) : Submodule ℂ A.H :=
  Submodule.span ℂ {v | ∃ ν ω, dist1 ν (lowK (sgnCN k r) μ) ≤ j ∧ dist1 ω (lowK (sgnCN k r) μ) ≤ j ∧
    v ∈ A.iso P ν ∧ IsWtOn (Formalism.REAL.Kset (sgnCN k r)) (A.onJ P) ω v}

def IsMeasSG (z : Fin (2 * r + k + 1) → ℂ) (μG μS ν : Measure (Mt k r)) : Prop :=
  IsHaarOn (UH (Hpk k r)) μG ∧ IsHaarOn (Sset k r z) μS ∧ IsQuotMeas μG μS ν

def HRep.mass (A : HRep k r) {W : Type} [NormedAddCommGroup W] (ν : Measure (Mt k r)) (B : A.H → W)
    (φ : Mat k r → ℝ) (w : A.H) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (φ (Matrix.of x)) * ‖B (A.σ (Matrix.of x) w)‖ₑ ^ 2 ∂ν

def HRep.IsIsoB (A : HRep k r) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (z : Fin (2 * r + k + 1) → ℂ)
    (c : ℂ) (π : Mat k r → (W →L[ℂ] W)) (ν : Measure (Mt k r)) (B : A.H → W) : Prop :=
  IsBesselMapSm z (psi k r z c) A.σ π B ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) A.σ, A.mass ν B (fun _ => 1) w = ‖w‖ₑ ^ 2

abbrev Idx (k r l : ℕ) := {I : Finset (Fin (2 * r + k + 1)) // I.card = l}

def minorIJ {l : ℕ} (M : Mat k r) (I J : Idx k r l) : ℂ :=
  (M.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)).det

def stdMat (dual : Bool) (P g : Mat k r) : Mat k r := if dual then ((P * g * P⁻¹)⁻¹)ᵀ else P * g * P⁻¹

def wtI (dual : Bool) {l : ℕ} (I : Idx k r l) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if a ∈ I.1 then (if dual then -1 else 1) else 0

def epsI {l : ℕ} (I : Idx k r l) : ℝ := ∏ a ∈ I.1, (if sgnCN k r a then (1 : ℝ) else -1)

def HRep.tens (A : HRep k r) (dual : Bool) (P : Mat k r) {l : ℕ} (g : Mat k r) (x : Idx k r l → A.H) :
    Idx k r l → A.H :=
  fun I => ∑ J, minorIJ (stdMat dual P g) I J • A.σ g (x J)

def HRep.hh (A : HRep k r) {l : ℕ} (x y : Idx k r l → A.H) : ℂ := ∑ I, (epsI I : ℂ) * ⟪y I, x I⟫_ℂ

def HRep.SmT (A : HRep k r) {l : ℕ} (x : Idx k r l → A.H) : Prop := ∀ I, x I ∈ smoothVecs (k := k) (r := r) A.σ

structure IsTensDec (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (dual : Bool) (P : Mat k r) (l : ℕ)
    (μ : Fin (2 * r + k + 1) → ℝ)
    (ι : ∀ I : Idx k r l, (R (μ + wtI dual I)).H → Idx k r l → (R μ).H)
    (p : ∀ I : Idx k r l, (Idx k r l → (R μ).H) → (R (μ + wtI dual I)).H) : Prop where
  ι_smooth : ∀ I, ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, (R μ).SmT (ι I y)
  p_smooth : ∀ I x, (R μ).SmT x → p I x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ
  ι_lin : ∀ I (a : ℂ), ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y' ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, ι I (a • y + y') = a • ι I y + ι I y'
  p_lin : ∀ I (a : ℂ) x x', (R μ).SmT x → (R μ).SmT x' → p I (a • x + x') = a • p I x + p I x'
  ι_equiv : ∀ I, ∀ g ∈ UH (Hpk k r), ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ι I ((R (μ + wtI dual I)).σ g y) = (R μ).tens dual P g (ι I y)
  sum_ι_p : ∀ x, (R μ).SmT x → ∑ I, ι I (p I x) = x
  p_ι_self : ∀ I, ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, p I (ι I y) = y
  p_ι_ne : ∀ I J, I ≠ J → ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual J)).σ, p I (ι J y) = 0
  ι_cont : ∀ I J (w : List (Mat k r)), (∀ X ∈ w, InLieHpk k r X) →
    IsCWCont (k := k) (r := r) (R (μ + wtI dual I)).σ (fun y => dsigW (R μ).σ w (ι I y J))
  p_cont : ∀ I (w : List (Mat k r)), (∀ X ∈ w, InLieHpk k r X) → ∃ (C : ℝ) (Ws : List (List (Mat k r))),
    (∀ w' ∈ Ws, ∀ X ∈ w', InLieHpk k r X) ∧ ∀ x, (R μ).SmT x →
      ‖dsigW (R (μ + wtI dual I)).σ w (p I x)‖ ≤ C * (Ws.map fun w' => ∑ J, ‖dsigW (R μ).σ w' (x J)‖).sum

def IsHHNorm (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (dual : Bool) (l : ℕ) (μ : Fin (2 * r + k + 1) → ℝ)
    (ι : ∀ I : Idx k r l, (R (μ + wtI dual I)).H → Idx k r l → (R μ).H) (ep : Idx k r l → ℝ) : Prop :=
  (∀ I, ep I = 1 ∨ ep I = -1) ∧
  (∀ I, ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, (R μ).hh (ι I x) (ι I y) = (ep I : ℂ) * ⟪y, x⟫_ℂ) ∧
  ∀ I J, I ≠ J → ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual J)).σ, (R μ).hh (ι I x) (ι J y) = 0

def omCoord (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1) (I : Idx k r l) : ℂ :=
  (Matrix.of fun a b : Fin l => (P *ᵥ fvec k r z (Fin.castLE hl b)) (I.1.orderEmbOfFin I.2 a)).det

def omCov (dual : Bool) (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1) (I : Idx k r l) : ℂ :=
  if dual then omCoord P z hl I else (epsI I : ℂ) * star (omCoord P z hl I)

def omB {H W : Type} [AddCommMonoid W] [Module ℂ W] (dual : Bool) (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ)
    {l : ℕ} (hl : l ≤ r + 1) (B : H → W) (x : Idx k r l → H) : W :=
  ∑ I, omCov dual P z hl I • B (x I)

def Amax (r : ℕ) (T κ b CA : ℝ) : ℝ := T * max κ κ⁻¹ ^ (2 * r) * b ^ CA

def H0 (k r : ℕ) (T κ b CA bv : ℝ) : ℝ :=
  (2 * r + k + 1 : ℕ) * Real.sqrt (Amax r T κ b CA) * (6 * bv) ^ (2 * r + 2)

def H1 (k r : ℕ) (T κ b CA bv : ℝ) : ℝ := H0 k r T κ b CA bv * max 1 (9 * (2 * r + k + 1 : ℕ) * bv / κ) ^ r

def Gam (k r : ℕ) (T T' κ b CA bv : ℝ) : ℝ :=
  2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * H1 k r T κ b CA bv * H1 k r T' κ b CA bv

theorem IsRange.gap_opp {lam : Fin (2 * r + k + 1) → ℝ} {c h q : ℝ} (H : IsRange k r lam c h q)
    {a b : Fin (2 * r + k + 1)} (hab : sgnCN k r a ≠ sgnCN k r b) : 100 * q ≤ |lam a - lam b| := by
  obtain ⟨hc, hg, hq, -⟩ := H
  rcases le_or_gt q 0 with h0 | h0
  · exact le_trans (by linarith) (abs_nonneg _)
  refine le_trans ?_ (hg a b hab)
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : 1 ≤ Real.sqrt (2 * r + 2) := Real.one_le_sqrt.2 (by linarith)
  have hm : c ≤ max 1 c := le_max_right _ _
  have h1 : c * (100 * q) ≤ 100 * max 1 c * q := by nlinarith
  have h2 : 100 * max 1 c * q ≤ 100 * max 1 c * q * Real.sqrt (2 * r + 2) :=
    le_mul_of_one_le_right (by positivity) hs
  exact le_of_mul_le_mul_left (h1.trans (h2.trans hq)) hc

theorem sgnCN_succ_ne {a b : Fin (2 * r + k + 1)} (ha : k - 1 ≤ a.val) (hb : b.val = a.val + 1) :
    sgnCN k r a ≠ sgnCN k r b := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ b.val < k - 1 := by omega
  simp only [sgnCN, h1, h2, if_false, ne_eq, decide_eq_decide]
  omega

theorem IsRange.le_bv {lam : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (hk : 1 ≤ k) (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) : 100 * q ≤ bv := by
  have h1 := H.gap_opp (sgnCN_succ_ne (a := ⟨k - 1, by omega⟩) (b := ⟨k, by omega⟩) le_rfl (by simp; omega))
  have h2 := S.2.2 ⟨k - 1, by omega⟩ le_rfl
  have h3 := S.2.2 ⟨k, by omega⟩ (by simp)
  refine h1.trans (abs_le.2 ⟨?_, ?_⟩) <;> linarith [h2.1, h2.2, h3.1, h3.2]

theorem IsRange.le_gap {lam : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) {a b : Fin (2 * r + k + 1)} (hab : a < b) : 100 * q ≤ lam a - lam b := by
  have hab' : a.val < b.val := hab
  have hpos : lam b < lam a := S.1.1 hab
  by_cases hb : b.val < k - 1
  · have h1 := H.2.2.2 a b hab hb
    rcases le_or_gt q 0 with h0 | h0
    · linarith
    · have : 1 ≤ max 1 c := le_max_left _ _
      nlinarith
  by_cases ha : a.val < k - 1
  · have h1 := H.le_bv (by omega) S
    have h2 := (S.2.1 a ha).1
    have h3 := (S.2.2 b (by omega)).2
    linarith
  · have hlt : a.val + 1 < 2 * r + k + 1 := by have := b.2; omega
    have h1 := H.gap_opp (sgnCN_succ_ne (a := a) (b := ⟨a.val + 1, hlt⟩) (by omega) rfl)
    have h2 : lam ⟨a.val + 1, hlt⟩ < lam a := S.1.1 (show a.val < a.val + 1 by omega)
    have h3 : lam b ≤ lam ⟨a.val + 1, hlt⟩ := S.1.1.antitone (show a.val + 1 ≤ b.val by omega)
    rw [abs_of_pos (by linarith)] at h1
    linarith

theorem abs_add_abs_le_dist1 {n : ℕ} (μ lam : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    |μ a - lam a| + |μ b - lam b| ≤ dist1 μ lam := by
  rw [← Finset.sum_pair (f := fun a => |μ a - lam a|) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

theorem InPP.gap_ge {lam μ : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (hμ : InPP lam q μ) (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) {a b : Fin (2 * r + k + 1)} (hab : a < b) :
    99 / 100 * (lam a - lam b) ≤ μ a - μ b := by
  have h1 := H.le_gap S hab
  have h2 := (abs_add_abs_le_dist1 μ lam hab.ne).trans hμ.2
  have h3 := neg_abs_le (μ a - lam a)
  have h4 := le_abs_self (μ b - lam b)
  linarith

theorem InPP.isHCParam {lam μ : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (hμ : InPP lam q μ) (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) : IsHCParam μ := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h1 := hμ.gap_ge S H hab
    have h2 : lam b < lam a := S.1.1 hab
    linarith
  · obtain ⟨m, hm⟩ := hμ.1 a
    obtain ⟨m', hm'⟩ := S.1.2 a
    exact ⟨m + m', by push_cast at *; linarith⟩

namespace Ex

open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def stdRep (k r : ℕ) : HRep k r where
  H := EuclideanSpace ℂ (Fin (2 * r + k + 1))
  σ := fun g => Matrix.toEuclideanCLM (𝕜 := ℂ) g

def detRep (k r : ℕ) (μ : Fin (2 * r + k + 1) → ℝ) : HRep k r where
  H := ℂ
  σ := fun g => (g.det ^ ⌊μ 0⌋₊) • ContinuousLinearMap.id ℂ ℂ

theorem detRep_apply (μ : Fin (2 * r + k + 1) → ℝ) (g : Mat k r) (v : ℂ) :
    (detRep k r μ).σ g v = g.det ^ ⌊μ 0⌋₊ * v := rfl

theorem contDiff_entry (i j : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g : Mat k r => g i j) :=
  (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin (2 * r + k + 1) → ℂ) i)

theorem contDiff_det : ContDiff ℝ ∞ (fun g : Mat k r => g.det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => ContDiff.mul contDiff_const (contDiff_prod fun i _ => contDiff_entry (s i) i)

theorem detRep_smooth (μ : Fin (2 * r + k + 1) → ℝ) (v : ℂ) :
    v ∈ smoothVecs (k := k) (r := r) (detRep k r μ).σ := by
  intro g₀ _
  refine ⟨Set.univ, fun g => g.det ^ ⌊μ 0⌋₊ * v, isOpen_univ, trivial, ?_, fun g _ _ => rfl⟩
  have h : ContDiff ℝ ∞ (fun g : Mat k r => g.det ^ ⌊μ 0⌋₊ * v) := (contDiff_det.pow _).mul contDiff_const
  exact h.contDiffOn

theorem detRep_dsigW (μ : Fin (2 * r + k + 1) → ℝ) (w : List (Mat k r)) :
    ∃ c : ℂ, ∀ v : ℂ, dsigW (k := k) (r := r) (H := ℂ) (detRep k r μ).σ w v = c * v := by
  induction w with
  | nil => exact ⟨1, fun v => by simp [dsigW]⟩
  | cons X w ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨deriv (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ ⌊μ 0⌋₊) 0 * c, fun v => ?_⟩
    have h1 : dsigW (k := k) (r := r) (H := ℂ) (detRep k r μ).σ (X :: w) v =
        deriv (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ ⌊μ 0⌋₊ *
          dsigW (k := k) (r := r) (H := ℂ) (detRep k r μ).σ w v) 0 := rfl
    rw [h1, hc, deriv_mul_const_field, mul_assoc]

theorem subsingleton_idx_top : Subsingleton (Idx k r (2 * r + k + 1)) :=
  ⟨fun I J => Subtype.ext (by
    rw [(Finset.card_eq_iff_eq_univ I.1).1 (by simpa using I.2),
      (Finset.card_eq_iff_eq_univ J.1).1 (by simpa using J.2)])⟩

attribute [local instance] subsingleton_idx_top

theorem idx_univ (I : Idx k r (2 * r + k + 1)) : I.1 = Finset.univ :=
  (Finset.card_eq_iff_eq_univ I.1).1 (by simpa using I.2)

theorem minor_top (M : Mat k r) (I : Idx k r (2 * r + k + 1)) : minorIJ M I I = M.det := by
  have hb : Function.Bijective (I.1.orderEmbOfFin I.2) :=
    (Finite.injective_iff_bijective).1 (I.1.orderEmbOfFin I.2).injective
  exact Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) M

theorem isTensDec_det (P : Mat k r) (hP : IsUnit P.det) (μ : Fin (2 * r + k + 1) → ℝ) (hμ : 0 ≤ μ 0) :
    IsTensDec (detRep k r) false P (2 * r + k + 1) μ (fun _ y _ => y) (fun I x => x I) where
  ι_smooth := fun _ y _ _ => detRep_smooth μ y
  p_smooth := fun I x _ => detRep_smooth _ (x I)
  ι_lin := fun _ _ _ _ _ _ => rfl
  p_lin := fun _ _ _ _ _ _ => rfl
  ι_equiv := by
    intro I g _ y _
    funext J
    have hJ : J = I := Subsingleton.elim _ _
    subst hJ
    have hu : (Finset.univ : Finset (Idx k r (2 * r + k + 1))) = {J} := by
      ext K; simp [Subsingleton.elim K J]
    have hw : (μ + wtI false J) 0 = μ 0 + 1 := by simp [wtI, idx_univ J]
    have hd : (stdMat false P g).det = g.det := by
      simp only [stdMat, Bool.false_eq_true, if_false]
      exact Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det P).2 hP) g
    simp only [HRep.tens, hu, Finset.sum_singleton, minor_top, hd]
    have key : ∀ y : ℂ, g.det ^ ⌊(μ + wtI false J) 0⌋₊ * y = g.det * (g.det ^ ⌊μ 0⌋₊ * y) := fun y => by
      rw [hw, Nat.floor_add_one hμ]; ring
    exact key y
  sum_ι_p := by
    intro x _
    funext J
    have hu : (Finset.univ : Finset (Idx k r (2 * r + k + 1))) = {J} := by
      ext K; simp [Subsingleton.elim K J]
    simp [hu]
  p_ι_self := fun _ _ _ => rfl
  p_ι_ne := fun I J h => absurd (Subsingleton.elim I J) h
  ι_cont := by
    intro I J w _
    obtain ⟨c, hc⟩ := detRep_dsigW μ w
    refine ⟨‖c‖, [[]], by simp, fun v _ => ?_⟩
    have := hc v
    simp only [List.map, List.sum_cons, List.sum_nil, add_zero, dsigW]
    erw [this]
    exact (norm_mul c v).le
  p_cont := by
    intro I w _
    obtain ⟨c, hc⟩ := detRep_dsigW (μ + wtI false I) w
    refine ⟨‖c‖, [[]], by simp, fun x _ => ?_⟩
    have hu : (Finset.univ : Finset (Idx k r (2 * r + k + 1))) = {I} := by
      ext K; simp [Subsingleton.elim K I]
    have := hc (x I)
    simp only [List.map, List.sum_cons, List.sum_nil, add_zero, dsigW, hu, Finset.sum_singleton]
    erw [this]
    exact (norm_mul c (x I)).le

theorem isHHNorm_det (μ : Fin (2 * r + k + 1) → ℝ) :
    IsHHNorm (detRep k r) false (2 * r + k + 1) μ (fun _ y _ => y) epsI := by
  refine ⟨fun I => ?_, fun I x _ y _ => ?_, fun I J h => absurd (Subsingleton.elim I J) h⟩
  · unfold epsI
    refine Finset.prod_induction _ (fun t : ℝ => t = 1 ∨ t = -1) ?_ (Or.inl rfl) ?_
    · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    · intro a _; split_ifs <;> simp
  · have hu : (Finset.univ : Finset (Idx k r (2 * r + k + 1))) = {I} := by
      ext K; simp [Subsingleton.elim K I]
    simp only [HRep.hh, hu, Finset.sum_singleton]
    rfl

theorem idx_top_nonempty : Nonempty (Idx k r (2 * r + k + 1)) := ⟨⟨Finset.univ, by simp⟩⟩

theorem subsingleton_idx_zero : Subsingleton (Idx k r 0) :=
  ⟨fun I J => Subtype.ext ((Finset.card_eq_zero.mp I.2).trans (Finset.card_eq_zero.mp J.2).symm)⟩

attribute [local instance] subsingleton_idx_zero

theorem isTensDec_zero (A : HRep k r) (dual : Bool) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) :
    IsTensDec (fun _ => A) dual P 0 μ (fun _ y _ => y) (fun I x => x I) := by
  have hu : ∀ J : Idx k r 0, (Finset.univ : Finset (Idx k r 0)) = {J} := fun J => by
    ext K; simp [Subsingleton.elim K J]
  exact
  { ι_smooth := fun I y hy J => hy
    p_smooth := fun I x hx => hx I
    ι_lin := fun I a y _ y' _ => rfl
    p_lin := fun I a x x' _ _ => rfl
    ι_equiv := fun I g _ y _ => by
      funext J
      simp [HRep.tens, minorIJ, hu J]
    sum_ι_p := fun x _ => by
      funext J
      simp [hu J]
    p_ι_self := fun I y _ => rfl
    p_ι_ne := fun I J h => (h (Subsingleton.elim _ _)).elim
    ι_cont := fun I J w hw => ⟨1, [w], by simpa using hw, fun v _ => by simp⟩
    p_cont := fun I w hw => ⟨1, [w], by simpa using hw, fun v _ => by simp [hu I]⟩ }

theorem shape_range : IsShape 1 0 ![-(1001/2), -(1999/2)] 500 ∧ IsRange 1 0 ![-(1001/2), -(1999/2)] 1 499 3 := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, one_pos, ?_, ?_, ?_⟩
  · intro a b h; fin_cases a <;> fin_cases b <;> simp_all <;> norm_num
  · intro a; fin_cases a
    · exact ⟨-501, by simp; norm_num⟩
    · exact ⟨-1000, by simp; norm_num⟩
  · intro i h; omega
  · intro i _; fin_cases i <;> simp <;> norm_num
  · intro a b h; fin_cases a <;> fin_cases b <;> simp_all [sgnCN] <;> norm_num [abs_of_pos, abs_of_neg]
  · have : Real.sqrt 2 ≤ 3/2 := by
      rw [Real.sqrt_le_iff]; norm_num
    simp; nlinarith
  · intro i j _ h; omega

example : (List.finRange 5).map (sgnCN 2 1) = [true, true, false, true, false] := by decide

end Ex

end GlobalTheory.Mom
