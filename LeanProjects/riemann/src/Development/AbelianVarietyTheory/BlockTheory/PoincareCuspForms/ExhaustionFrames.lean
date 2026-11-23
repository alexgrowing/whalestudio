import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped Matrix ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsOrthonormalFrame (X : Data E r) (x0 : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x0 τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def Base (X : Data E r) : Type := {x0 : Frame X.Ψ r // IsOrthonormalFrame X x0}

instance instNonemptyBase (X : Data E r) : Nonempty (Base X) :=
  ⟨⟨fun τ => (X.signature τ).choose, fun τ => (X.signature τ).choose_spec.2⟩⟩

variable (X : Data E r)

def zBlock (z : V (nd X)) (τ : X.Ψ) :
    Matrix {a : Fin r // X.p0 ≤ (a : ℕ)} {b : Fin r // (b : ℕ) < X.p0} ℂ :=
  Matrix.of fun a b => nmat X z τ a.1 b.1

def zFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then nmat X z τ a b else if a = b then 1 else 0

def leviFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then 0 else nmat X z τ a b

def nFrame (z : V (nd X)) : Frame X.Ψ r := rmul (zFrame X z) (leviFrame X z)

def point (x0 : Base X) (z : V (nd X)) : Frame X.Ψ r := rmul x0.1 (nFrame X z)

def zNorm (z : V (nd X)) (τ : X.Ψ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (zBlock X z τ))‖

def Om : Set (V (nd X)) := {z | ∀ τ : X.Ψ, zNorm X z τ < 1}

def zDet (z : V (nd X)) (τ : X.Ψ) : ℝ := ((1 - (zBlock X z τ)ᴴ * zBlock X z τ).det).re

def rho (z : V (nd X)) : ℝ := ∑ τ : X.Ψ, -Real.log (zDet X z τ)

def pIdx : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

def rel (x0 : Base X) (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat x0.1 τ)⁻¹ * mat x τ

def bigCell (x0 : Base X) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ : X.Ψ, ∏ i : Fin r, lminor (rel X x0 x τ) i.succ

def rhoFrame (x0 : Base X) (x : X.dom) : ℝ :=
  ∑ τ : X.Ψ, (-Real.log ‖dmin X.Gm x.1 τ (pIdx X)‖ +
    Real.log (‖lminor (rel X x0 x.1 τ) (pIdx X)‖ ^ 2))

def leviSq (z : V (nd X)) (τ : X.Ψ) : ℝ :=
  ∑ a : Fin r, ∑ b : Fin r, if b < a then ‖leviFrame X z τ a b‖ ^ 2 else 0

def exhaustion (z : V (nd X)) : ℝ := rho X z + ∑ τ : X.Ψ, Real.log (1 + leviSq X z τ)

def OmOff (g : V (nd X) → ℂ) : Set (V (nd X)) := {z | z ∈ Om X ∧ g z ≠ 0}

def exhaustionOff (g : V (nd X) → ℂ) (z : V (nd X)) : ℝ := exhaustion X z + (‖g z‖ ^ 2)⁻¹

def density (x0 : Base X) (z : V (nd X)) : ℝ :=
  ∏ τ : X.Ψ, ∏ i : Fin r, (‖dmin X.Gm (point X x0 z) τ i.castSucc‖ ^ 2)⁻¹

def mu (x0 : Base X) : Measure (V (nd X)) :=
  (volume.restrict (Om X)).withDensity fun z => ENNReal.ofReal (density X x0 z)

def kappa (b : ℝ) (z : V (nd X)) : ℝ := Real.exp (-b * rho X z)

def kappaFrame (x0 : Base X) (b : ℝ) (x : X.dom) : ℝ := Real.exp (-b * rhoFrame X x0 x)

def image (x0 : Base X) (C : Set (Frame X.Ψ r)) : Set (V (nd X)) :=
  {z | z ∈ Om X ∧ ∃ b ∈ Bor X.Ψ r, rmul (point X x0 z) b ∈ C}

def evidence (x0 : Base X) (P : Frame X.Ψ r → ℂ) (z : V (nd X)) : ℂ := P (point X x0 z)

def phi (x0 : Base X) (la : Wt X.Ψ r) (z : V (nd X)) : ℝ :=
  ∑ τ : X.Ψ, ∑ i : Fin r, (la τ i : ℝ) *
    Real.log ‖dmin X.Gm (point X x0 z) τ i.succ / dmin X.Gm (point X x0 z) τ i.castSucc‖

def poincTerm (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (γ : X.Γ) (x : Frame X.Ψ r) : ℂ :=
  (X.χ la γ.1)⁻¹ * P (lact γ.1 x)

def poinc (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑' γ : X.Γ, poincTerm X la P γ x

def PoincConv (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ x ∈ X.dom, Summable fun γ : X.Γ => poincTerm X la P γ x

def PoincNormal (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ C ⊆ X.dom, IsCompact C → ∃ u : X.Γ → ℝ, Summable u ∧
    ∀ γ : X.Γ, ∀ x ∈ C, ‖poincTerm X la P γ x‖ ≤ u γ

theorem zDet_pos {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) : 0 < zDet X z τ := by
  set Z := zBlock X z τ with hZ
  have hn : zNorm X z τ < 1 := hz τ
  have hquad : ∀ x, star x ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ x) = star x ⬝ᵥ x - star (Z *ᵥ x) ⬝ᵥ (Z *ᵥ x) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hsq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ), star v ⬝ᵥ v = ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : ℂ) := by
    intro ι _ v
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
    rw [Complex.ofReal_pow]
    exact h
  have hpd : (1 - Zᴴ * Z).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    · intro x hx
      rw [hquad, hsq, hsq, ← Complex.ofReal_sub, Complex.zero_lt_real, sub_pos]
      have hx0 : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
      have hle : ‖WithLp.toLp 2 (Z *ᵥ x)‖ ≤ zNorm X z τ * ‖WithLp.toLp 2 x‖ :=
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm (WithLp.toLp 2 x)
      have hlt : ‖WithLp.toLp 2 (Z *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ :=
        lt_of_le_of_lt hle (by nlinarith [norm_nonneg (WithLp.toLp 2 (Z *ᵥ x))])
      exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  have hdet := hpd.det_pos
  exact (Complex.lt_def.mp hdet).1

end

end GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
