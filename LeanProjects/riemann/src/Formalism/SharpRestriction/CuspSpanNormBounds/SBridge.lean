import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Bridge

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

def orbSqO {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) : ℝ≥0∞ :=
  ⨆ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
    (_ : IsPtRepO L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν),
    ENNReal.ofReal (hsNormSq (OrbInt L F g ν))

def kaS (D : D7) : ℝ := D.host.ka / gg D

section

variable (D : D7) (large₂ : SizeData₂ D)

def AmpIsBessel (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (_ : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3)
    (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (f : Mx D.R.k D.R.rS →
        ((toBessel D τ w w' θ W lam' A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W lam' A hW hA hT hT').Wp))
      (K : ℝ), 0 < K ∧ IsKFinCoefH (toBessel D τ w w' θ W lam' A hW hA hT hT').σ f ∧
      (∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec ≠ 0 ∧
        ENNReal.ofReal K * jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec ≤ MMv D w w' A μsec) ∧
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        ENNReal.ofReal (hsNormSq (A.J νR γ)) ≤
          ENNReal.ofReal (K * large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) *
            orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p

def FrameChange (Ch Cs Cn Cf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (ka b : ℝ),
    Real.exp 1 ≤ b → 0 < ka → ka ≤ b ^ Ch → ka⁻¹ ≤ b ^ Ch → L.c = ((2 * ka : ℝ) : ℂ) → L.κN ≠ ⊤ →
    L.ε = epsSH D.R → 0 < L.κN →
    StdHyp Ch Cs D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') ka b →
    l1dist L.lam lam0 ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    IsKFinCoefH L.σ f →
    ∃ (L₁ : LocBessel D.R.k D.R.rS) (f₁ : Mx D.R.k D.R.rS → (L₁.Wq →L[ℂ] L₁.Wp)),
      L₁.ε = L.ε ∧ L₁.lam = L.lam ∧ L₁.u = L.u ∧ L₁.u' = L.u' ∧ L₁.c = cOfDpsi ((1 : ℝ) : ℂ) ∧ 0 < L₁.κN ∧ L₁.κN ≠ ⊤ ∧
      Tz D.R.k D.R.rS L₁.z = Tz D.R.k D.R.rS L.z * ka ^ (2 * D.R.rS) ∧
      Tz D.R.k D.R.rS L₁.z' = Tz D.R.k D.R.rS L.z' * ka ^ (2 * D.R.rS) ∧
      IsKFinCoefH L₁.σ f₁ ∧
      ∀ μsec, IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ μsec₁, IsSection D.R.k D.R.rS L₁.z L₁.z' μsec₁ ∧
        ∃ K₁ : ℝ, 0 < K₁ ∧
        jNorm2 L₁ f₁ μsec₁ ≤ ENNReal.ofReal K₁ * jNorm2 L f μsec ∧
        (jNorm2 L f μsec ≠ 0 → jNorm2 L₁ f₁ μsec₁ ≠ 0) ∧
        ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
          ∃ p₁ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁ ≠ 0 ∧
            max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) ≤
              b ^ (Cf * (D.R.m : ℝ) ^ 2) * max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ∧
            ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSqO L f p ≤
              ENNReal.ofReal (b ^ (Cf * (D.R.m : ℝ) ^ 2) *
                ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁

def StdOfHyp (C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tr D w) (Tr D w') (kaS D)
      (large₂.sc.b ^ Cβ) ∧
    AllGaps (lamD D τ) (Cs' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)

def GfOfRelPt : Prop :=
  ∀ (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)),
    RelPt D z z' γ p → Gf D.R.k D.R.rS z z' γ = Gpt (Tz D.R.k D.R.rS z) (Tz D.R.k D.R.rS z') p

end

def toBesselK (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') : LocBessel D.R.k D.R.rS :=
  { toBessel D τ w w' θ W lam A hW hA hT hT' with c := cOfDpsi ((kaS D : ℝ) : ℂ) }

section

variable (D : D7) (large₂ : SizeData₂ D)

def MomNorm : Prop :=
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (Bf : A.H → W.Wp) (P : Mx D.R.k D.R.rS) (w0 : A.H),
      IsBesselMapSm W.z (psi D.R.k D.R.rS W.z (cOfDpsi ((kaS D : ℝ) : ℂ))) A.σ W.π Bf ∧
      (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
        l2SG W.νS (fun g => Bf (A.σ g v)) = (‖v‖₊ : ℝ≥0∞) ^ 2) ∧
      IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
      w0 ∈ shell (toBesselK D τ w w' θ W lam' A hW hA hT hT') P 0 ∧ w0 ≠ 0 ∧
      ∀ F : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable F →
        ∫⁻ x, F (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
          l2SG W.νS A.Φ * Emom (toBesselK D τ w w' θ W lam' A hW hA hT hT') Bf W.νS w0
            (fun g => F (fun a => lA D.R.k D.R.rS W.z g a))

def MomNormR (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (Bf : A.H → W.Wp) (P : Mx D.R.k D.R.rS) (w0 : A.H),
      IsBesselMapSm W.z (psi D.R.k D.R.rS W.z (cOfDpsi ((kaS D : ℝ) : ℂ))) A.σ W.π Bf ∧
      (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
        l2SG W.νS (fun g => Bf (A.σ g v)) = (‖v‖₊ : ℝ≥0∞) ^ 2) ∧
      IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
      w0 ∈ shell (toBesselK D τ w w' θ W lam' A hW hA hT hT') P 0 ∧ w0 ≠ 0 ∧
      ∀ F : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable F →
        ∫⁻ x, F (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
          l2SG W.νS A.Φ * Emom (toBesselK D τ w w' θ W lam' A hW hA hT hT') Bf W.νS w0
            (fun g => F (fun a => lA D.R.k D.R.rS W.z g a))

def BesselSchur : Prop :=
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W),
    GoodS D lam' A → ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

def MuSHaar : Prop :=
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → IsHaarOn (Sset D.R.k D.R.rS W.z) (muS W.μW W.μN)

def RangeOfHyp (C' Cl Cg cb Cu cT CT C0 Cs Cn Cq Cq0 Cr : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w, ∃ bv : ℝ, Cs * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS (uS D w τ) (lamD D τ) bv ∧
    ∀ (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
      (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
      l1dist lam' (lamD D τ) + (((2 * D.R.rS + 2) * q : ℕ) : ℝ) ≤ q0 Cq0 (2 * D.R.rS + 2) (epsSH D.R) (uS D w τ) (lamD D τ) ∧
      (((2 * D.R.rS + 2) * q + 0 : ℕ) : ℝ) ≤ bv / (Cr * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 4)

end

section

variable (D : D7) (large₂ : SizeData₂ D)

def DegStep (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ μ, l1dist μ (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1 →
    ∀ (A A' : LocS W) (i : Fin (2 * D.R.rS + D.R.k + 1)), GoodS D μ A → GoodS D (μ + Pi.single i 1) A' →
      ∃ (P : Mx D.R.k D.R.rS)
        (X : TensorDS (2 * D.R.rS + D.R.k + 1) (epsSH D.R) μ A.H (fun g => A.σ (P⁻¹ * g * P)))
        (v : A.H) (vs : X.Hs i),
        IsDS (epsSH D.R) μ (fun g => A.σ (P⁻¹ * g * P)) ∧
        (∀ v w : A.H, IsKFin (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) v →
          IsKFin (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) w →
          MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) =>
            (frob (umat g) : ℂ) * coefOn (fun g => A.σ (P⁻¹ * g * P)) v w g) 2 (Formalism.REAL.muG (epsSH D.R))) ∧
        i ∈ X.Sm ∧ v ≠ 0 ∧ vs ≠ 0 ∧
        A'.deg / A.deg = fdegOf (Formalism.REAL.muG (epsSH D.R)) (X.σs i) vs /
          fdegOf (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) v

def ProdBound (C' Cl Cg cb Cu cT CT C0 Cn C : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist μ (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1 →
    ∀ i, (D.R.r : ℝ) ^ (-C) ≤ ∏ s' ∈ Finset.univ.erase i, (μ i + 1 - μ s') / (μ i - μ s') ∧
      ∏ s' ∈ Finset.univ.erase i, (μ i + 1 - μ s') / (μ i - μ s') ≤ (D.R.r : ℝ) ^ C

end

theorem sum_castLE {N l : ℕ} (hl : l ≤ N) (f : Fin N → ℂ) (hf : ∀ i : Fin N, l ≤ i.val → f i = 0) :
    ∑ i, f i = ∑ i : Fin l, f (Fin.castLE hl i) := by
  classical
  have h1 : ∑ i ∈ Finset.univ.map (⟨Fin.castLE hl, Fin.castLE_injective hl⟩ : Fin l ↪ Fin N), f i =
      ∑ i, f i := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    refine hf i ?_
    by_contra h
    exact hi (Finset.mem_map.2 ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [← h1, Finset.sum_map]
  try rfl

theorem leadMinor_cell {N : ℕ} (L P U : Matrix (Fin N) (Fin N) ℂ) (hL : IsLoUni L) (hU : IsUpUni U) (l : ℕ)
    (hl : l ≤ N) : leadMinor (L * P * U) l hl = leadMinor P l hl := by
  unfold leadMinor
  have hLs : ∀ (i : Fin l) (a : Fin N), l ≤ a.val → L (Fin.castLE hl i) a = 0 := fun i a ha =>
    (hL (Fin.castLE hl i) a).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le i.isLt ha))
  have hUs : ∀ (b : Fin N) (j : Fin l), l ≤ b.val → U b (Fin.castLE hl j) = 0 := fun b j hb =>
    (hU b (Fin.castLE hl j)).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.isLt hb))
  have key : (L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      L.submatrix (Fin.castLE hl) (Fin.castLE hl) * P.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [sum_castLE hl]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [sum_castLE hl]
      intro a ha
      rw [hLs i a ha, zero_mul]
    · intro b hb
      rw [hUs b j hb, mul_zero]
  have hLt : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact (hL (Fin.castLE hl i) (Fin.castLE hl j)).1 (OrderDual.toDual_lt_toDual.mp hij)
  have hUt : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    exact (hU (Fin.castLE hl i) (Fin.castLE hl j)).1 hij
  have h1 : ∏ i : Fin l, L.submatrix (Fin.castLE hl) (Fin.castLE hl) i i = 1 :=
    Finset.prod_eq_one (fun i _ => (hL (Fin.castLE hl i) (Fin.castLE hl i)).2 rfl)
  have h2 : ∏ i : Fin l, U.submatrix (Fin.castLE hl) (Fin.castLE hl) i i = 1 :=
    Finset.prod_eq_one (fun i _ => (hU (Fin.castLE hl i) (Fin.castLE hl i)).2 rfl)
  rw [key, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular (M := L.submatrix (Fin.castLE hl) (Fin.castLE hl)) hLt,
    Matrix.det_of_upperTriangular (M := U.submatrix (Fin.castLE hl) (Fin.castLE hl)) hUt, h1, h2,
    one_mul, mul_one]

theorem normSq_leadMinor_ZhatO (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (l : ℕ) (hl : l ≤ r + 1) :
    Complex.normSq (leadMinor (ZhatO k r z z' g) l hl) = Complex.normSq (leadMinor (Formalism.QuantumDeterminants.Zhat k r z z' g) l hl) := by
  unfold leadMinor
  have e : (ZhatO k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      (Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (r - (Fin.castLE hl b).val)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, ZhatO]
    ring
  have hp : Complex.normSq (∏ b : Fin l, (-1 : ℂ) ^ (r - (Fin.castLE hl b).val)) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one (fun b _ => by rw [map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow])
  rw [e, Matrix.det_mul, Complex.normSq_mul, Matrix.det_diagonal]
  simp only [hp, mul_one]

theorem gfOfRelPt (D : D7) : GfOfRelPt D := by
  unfold GfOfRelPt
  intro z z' γ p hp
  obtain ⟨-, ⟨L, U, hL, hU, hZ⟩, -⟩ := hp
  have hm : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (leadMinor (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ) l hl) =
        Complex.normSq (leadMinor (ptMat p) l hl) := by
    intro l hl
    rw [← normSq_leadMinor_ZhatO, hZ, leadMinor_cell L (ptMat p) U hL hU]
  unfold Gf Gpt
  rw [← hm, ← hm]
  rfl

end Formalism.MainNotions.S.Bridge

end
