import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
import Formalism.FlagUnipotentLattices.BlockMinorAbsoluteFromExplicit
import Formalism.FormalDegreeBessel.FinalDS
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.TheoremBConstants

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BesselShellMomentBounds

section PieceA1

def LitFormalDegree : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), IsHCParam lam → IsDS ε lam σ → v ≠ 0 →
      fdegOf (Formalism.REAL.muG ε) σ v = c * fdegHC lam

end PieceA1

section PieceA2

def OrbDat {k r : ℕ} (L : LocBessel k r) : Type :=
  {x : Point ℂ (r + 1) × Mx k r × Measure (Mt k r) × Measure (PairSp k r) //
    Gpt (Tz k r L.z) (Tz k r L.z') x.1 ≠ 0 ∧ IsPtRep L x.1 x.2.1 ∧ IsRelStab L x.2.1 ∧
      IsRootMeas L x.1 x.2.1 x.2.2.1 ∧ IsOrbQuot L x.2.1 x.2.2.1 x.2.2.2}

def OneStepCellExpansion (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ → BesselRangeNearParameter D Cg Cq L lam0 p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℤ) (l : Fin (D.R.rS + 1)) (sg : Bool),
      ∑ s, |(μ s : ℝ)| + ((l : ℕ) + 1 : ℕ) ≤ ((D.R.rS + 1) * p : ℕ) →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) →₀ ℂ,
        (∀ ν ∈ a.support, ∑ s, |(ν s : ℝ)| ≤ ((l : ℕ) + 1 : ℕ)) ∧
        (a.sum fun _ c => ‖c‖) ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) ∧
        (∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q →
          (if sg then Dbig ((l : ℕ) + 1) q else star (Dbig ((l : ℕ) + 1) q)) •
              L.J (fν μ) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            a.sum fun ν c => c • L.J (fν (μ + ν)) (bigCell D.R.k D.R.rS q.1 (μsec q.2))) ∧
        (LocOk D Ch Cg L lam0 ka b κ →
          ((D.R.rS + 1 : ℕ) : ℝ) * (l1 L.lam lam0 + (((D.R.rS + 1) * p : ℕ) : ℝ)) ≤
            hNC L.ε lam0 / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)) →
        ∀ x : OrbDat L,
          (if sg then Dpt x.1.1 l else star (Dpt x.1.1 l)) • OrbInt L (fν μ) x.1.2.1 x.1.2.2.2 =
            a.sum fun ν c => c • OrbInt L (fν (μ + ν)) x.1.2.1 x.1.2.2.2)

end PieceA2

section PieceA3

def PieriShellBound (D : D7) (Ch Cg Cq C1 CA CQ : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs) (j : ℕ),
    CloudNodeShape D Ch Cg L lam0 ka b bv Bf μG μS νq P w j →
    l1 L.lam lam0 + 1 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
    (j : ℝ) + 2 ≤ bv / (C1 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2) →
    ∃ (X : Fin (2 * D.R.rS + D.R.k + 1) → Mx D.R.k D.R.rS → ℝ) (ιs : Type) (_ : Fintype ιs)
      (sI : ιs → Fin (2 * D.R.rS + D.R.k + 1)) (A : ιs → ℝ) (Ls : ιs → LocBessel D.R.k D.R.rS)
      (Bs : ∀ s, (Ls s).Hs → (Ls s).Wp) (Ps : ιs → Mx D.R.k D.R.rS)
      (ws : ∀ (_c : Fin (2 * D.R.rS + D.R.k + 1)) (s : ιs), (Ls s).Hs),
      Fintype.card ιs ≤ 2 * D.R.rS + D.R.k + 1 ∧
      (∀ c g, 0 ≤ X c g) ∧ (∀ g ∈ UH (Hpk D.R.k D.R.rS), la D L 0 g ^ 2 = ∑ c, X c g) ∧
      (∀ s, 0 ≤ A s ∧ A s ≤ Tz D.R.k D.R.rS L.z * ka ^ (2 * D.R.rS) * b ^ CA) ∧
      (∀ s, (Ls s).lam = L.lam - Pi.single (sI s) 1 ∧ (Ls s).u = L.u ∧ (Ls s).z = L.z ∧
        ShellCommonHypotheses D Ch Cg (Ls s) lam0 ka b bv (Bs s) μG μS νq (Ps s)) ∧
      (∀ c s, ws c s ∈ shell (Ls s) (Ps s) (j + 2)) ∧
      (∀ c, ∀ g ∈ UH (Hpk D.R.k D.R.rS), X c g * ‖Bf (L.σ g w)‖ ^ 2 ≤
        (Fintype.card ιs : ℝ) * ∑ s, A s * ‖Bs s ((Ls s).σ g (ws c s))‖ ^ 2) ∧
      ∀ c, ∑ s, ‖ws c s‖ ^ 2 ≤
        (CQ * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * b) ^ (2 * (2 * D.R.rS + 2) + 1) * ‖w‖ ^ 2

end PieceA3

section PieceA4

open Formalism.HermitianLatticeCounting.ExpansionTerms

section Geo

variable {k r : ℕ}

end Geo

def DerivedActionPhaseBound (D : D7) (Ch Cg Cq Cs : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS),
    ShellCommonHypotheses D Ch Cg L lam0 ka b bv Bf μG μS νq P →
    l1 L.lam lam0 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
    ∃ Eop : Fin (2 * D.R.rS + D.R.k + 1) × Fin (2 * D.R.rS + D.R.k + 1) → L.Hs → L.Hs,
      (∀ i j w, w ∈ shell L P j → Eop i w ∈ shell L P (j + 2)) ∧
      (∀ (j : ℕ) w, w ∈ shell L P j →
        ∑ i, ‖Eop i w‖ ^ 2 ≤ (Cs * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 * (b + j)) ^ 2 * ‖w‖ ^ 2) ∧
      ∀ (Y : Mx D.R.k D.R.rS) (θ : ℝ), Y * Y * Y = 0 →
        (∀ t : ℝ, (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) ∈ Nset D.R.k D.R.rS ∧
          psi D.R.k D.R.rS L.z L.c (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) =
            Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I)) →
        ∀ (j : ℕ) w, w ∈ shell L P j → ∀ g ∈ UH (Hpk D.R.k D.R.rS),
          ((θ : ℂ) * Complex.I) • Bf (L.σ g w) = ∑ i, (g⁻¹ * Y * g) i.1 i.2 • Bf (L.σ g (Eop i w))

end PieceA4

section PieceB1

def BpAll (D : D7) (Ch Cg Cb : ℝ)
    (Near : (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → Prop) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → Near L.lam lam0 →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ

def FrC (D : D7) (Cf ka : ℝ) : ℝ :=
  max ka⁻¹ (ka⁻¹)⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) *
    max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ))

def GsC (D : D7) (ka : ℝ) : ℝ := ka⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (ka ^ D.R.rS) ^ (4 * (D.R.rS + 1))

def GapFr (D : D7) (Cgf : ℝ) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) : Prop :=
  GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3))

theorem bp_in_frame (D : D7) (Ch Cg Cgf Cf Cb : ℝ)
    (Near : (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → Prop)
    (hFr : FrameBesselBound D Cgf Cf) (hBp : BpAll D Ch Cg Cb Near)
    (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b : ℝ) (hL : LocOk D Ch Cg L lam0 ka b ka) (hN : Near L.lam lam0) (hgap : GapFr D Cgf L.ε L.lam)
    (hf : IsKFinCoefH L.σ f) (hsec : IsSection D.R.k D.R.rS L.z L.z' μsec)
    (γ : Point ℂ (D.R.rS + 1)) (hG : Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0) :
    ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ ≤
      ENNReal.ofReal (FrC D Cf ka * (b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) *
        (max 1 (1 / (GsC D ka * Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ))) ^
          (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2))) * jNorm2 L f μsec := by
  obtain ⟨hk, hε, hc, hκ0, hκt, hStd, hT1, hT1'⟩ := hL
  have hka : 0 < ka := hStd.2.2.2.1
  have hτ : 0 < ka ^ D.R.rS := pow_pos hka _
  obtain ⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, hf₁, hrest⟩ :=
    hFr L f ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) hτ hc hκ0 hκt hε hgap hf
  obtain ⟨μsec₁, hsec₁, K₁, hK₁, hJ₁, hpt⟩ := hrest μsec hsec
  obtain ⟨γ₁, -, hG₁, -, hle⟩ := hpt γ hG
  have hsq : (ka ^ D.R.rS) ^ 2 = ka ^ (2 * D.R.rS) := by rw [← pow_mul, mul_comm]
  have hinv : ka ^ (2 * D.R.rS) * (1 / ka) ^ (2 * D.R.rS) = 1 := by
    rw [← mul_pow, mul_one_div, div_self hka.ne', one_pow]
  have hone : (ka / ka) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hL₁ : LocOk D Ch Cg L₁ lam0 ka b 1 := by
    refine ⟨hk, e1.trans hε, ?_, e6, e7, ?_, ?_, ?_⟩
    · rw [e5, inv_mul_cancel₀ hka.ne']
    · rw [e1, e3, e4, e8, e9, hsq]
      have a1 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      have a2 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z' * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z' * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      rw [a1, a2]
      exact hStd
    · rw [e8, hsq, one_pow, mul_one, mul_comm]; exact hT1
    · rw [e9, hsq, one_pow, mul_one, mul_comm]; exact hT1'
  have hG₁0 : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0 := by
    rw [hG₁]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hka.ne')) (pow_ne_zero _ hτ.ne')) hG
  have hB := hBp L₁ lam0 f₁ μsec₁ ka b hL₁ (by rw [e2]; exact hN) hf₁ hsec₁ γ₁ hG₁0
  unfold BpIneq at hB
  rw [hG₁, hJ₁] at hB
  have hK0 : ENNReal.ofReal K₁ ≠ 0 := (ENNReal.ofReal_pos.2 hK₁).ne'
  have hKt : ENNReal.ofReal K₁ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hF0 : 0 ≤ FrC D Cf ka := by unfold FrC; positivity
  have h2 := hle.trans (mul_le_mul' le_rfl hB)
  rw [← ENNReal.mul_le_mul_iff_right hK0 hKt]
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hF0]
  unfold FrC GsC
  ring

end PieceB1

section PieceB2

theorem prod_one_add_pow {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι] (x : ι → R) (N : ι → ℕ) :
    ∏ l, (1 + x l) ^ N l =
      ∑ κ ∈ Fintype.piFinset (fun l => Finset.range (N l + 1)), ∏ l, ((N l).choose (κ l) : R) * x l ^ κ l := by
  rw [Finset.prod_congr rfl (fun l _ => (show (1 + x l) ^ N l =
      ∑ k ∈ Finset.range (N l + 1), ((N l).choose k : R) * x l ^ k by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, mul_comm]))]
  exact Finset.prod_univ_sum _ _

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_bound {ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → (Wq →L[ℂ] Wp)) (M : ℝ)
    (hM : ∀ i ∈ s, hsNormSq (x i) ≤ M) : hsNormSq (∑ i ∈ s, a i • x i) ≤ (∑ i ∈ s, ‖a i‖) ^ 2 * M := by
  refine (hsNormSq_sum_le s a x).trans ?_
  have h1 : ∑ i ∈ s, ‖a i‖ * hsNormSq (x i) ≤ (∑ i ∈ s, ‖a i‖) * M := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM i hi) (norm_nonneg _)
  calc (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * hsNormSq (x i) ≤ (∑ i ∈ s, ‖a i‖) * ((∑ i ∈ s, ‖a i‖) * M) :=
        mul_le_mul_of_nonneg_left h1 (Finset.sum_nonneg fun i _ => norm_nonneg (a i))
    _ = (∑ i ∈ s, ‖a i‖) ^ 2 * M := by ring

end HS

section Loc

variable {k r : ℕ}

theorem OrbInt_smul (L : LocBessel k r) (c : ℂ) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r)
    (ν : Measure (PairSp k r)) : OrbInt L (fun x => c • F x) g ν = c • OrbInt L F g ν := by
  unfold OrbInt besselIntg
  rw [← integral_smul]
  congr 1
  funext p
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

def withRep (L : LocBessel k r) (lam' : Fin (2 * r + k + 1) → ℝ) (hlam' : IsHCParam lam') (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ' : Mx k r → (H →L[ℂ] H))
    (hσ' : IsDSHpk k r L.ε lam' σ') : LocBessel k r where
  ε := L.ε
  lam := lam'
  hlam := hlam'
  z := L.z
  z' := L.z'
  hz := L.hz
  hz' := L.hz'
  u := L.u
  u' := L.u'
  Hs := H
  σ := σ'
  hσ := hσ'
  Wp := L.Wp
  π := L.π
  hπ := L.hπ
  Wq := L.Wq
  π' := L.π'
  hπ' := L.hπ'
  c := L.c
  μW := L.μW
  μW' := L.μW'
  hμW := L.hμW
  hμW' := L.hμW'
  κN := L.κN

end Loc

def ExFamC (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (f0 : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ → BesselRangeNearParameter D Cg Cq L lam0 p →
    IsSection D.R.k D.R.rS L.z L.z' μsec → IsKFinCoefH L.σ f0 → jNorm2 L f0 μsec = 1 →
    ∃ (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) (_ : ∀ ν, NormedAddCommGroup (Hν ν))
      (_ : ∀ ν, InnerProductSpace ℂ (Hν ν)) (_ : ∀ ν, CompleteSpace (Hν ν))
      (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
        Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)), fν 0 = f0 ∧
      ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
        IsHCParam (L.lam + fun a => (ν a : ℝ)) ∧
        IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
        (jNorm2 L (fν ν) μsec = 1 ∨
          ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
            ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
              ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))

theorem jNorm2_le_one_of_alt (D : D7) (L : LocBessel D.R.k D.R.rS) (F : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (h : jNorm2 L F μsec = 1 ∨
      (∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J F (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0)) :
    jNorm2 L F μsec ≤ 1 := by
  have hk2 : 2 ≤ D.R.k := by have := Ranks.k_ge D.R; omega
  rcases h with h | h
  · exact le_of_eq h
  · rw [jNorm2_eq]
    have : ∀ q, ENNReal.ofReal (BesselShellMomentBounds.dens L F μsec q) = 0 := fun q => by
      unfold BesselShellMomentBounds.dens
      by_cases hq : (∀ i, q.1 i ≠ 0) ∧ Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2
      · rw [h q hq]
        simp [hsNormSq_eq]
      · simp [bcWeight_off (k := D.R.k) (r := D.R.rS) hk2 (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') q hq]
    simp [this]

end PieceB2

section PieceB3

def KKc (D : D7) (Cf Cb ka b G : ℝ) : ℝ :=
  FrC D Cf ka * (b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) *
    (max 1 (1 / (GsC D ka * G))) ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2))

theorem KKc_pos (D : D7) (Cf Cb ka b G : ℝ) (hka : 0 < ka) (hb : 0 < b) : 0 < KKc D Cf Cb ka b G := by
  unfold KKc FrC GsC
  positivity

theorem loc_one (D : D7) (Ch Cg Cg1 Cq Cgf Cf Cb1 Cb2 : ℝ)
    (Near : (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → Prop)
    (hFr : FrameBesselBound D Cgf Cf) (hBp : BpAll D Ch Cg Cb2 Near) (h92 : BesselConjugatesEveryCell D Ch Cg1 Cq Cb1)
    (hX : ExFamC D Ch Cg1 Cq)
    (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b : ℝ) (hb : 0 < b) (hL : LocOk D Ch Cg L lam0 ka b ka) (hL1 : LocOk0 D Ch Cg1 L lam0 ka b ka)
    (hf : IsKFinCoefH L.σ f) (hsec : IsSection D.R.k D.R.rS L.z L.z' μsec)
    (N : Fin (D.R.rS + 1) → ℕ) (s : Fin (D.R.rS + 1) → ℝ) (hs : ∀ l, 0 ≤ s l)
    (hR : BesselRangeNearParameter D Cg1 Cq L lam0 (2 * ∑ l, N l))
    (hLc : LocOk D Ch Cg1 L lam0 ka b ka)
    (hF2 : ((D.R.rS + 1 : ℕ) : ℝ) * (l1 L.lam lam0 + (((D.R.rS + 1) * (2 * ∑ l, N l) : ℕ) : ℝ)) ≤
      hNC L.ε lam0 / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)))
    (hNear : ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      ∑ t, |(ν t : ℝ)| ≤ ((D.R.rS + 1) * (2 * ∑ l, N l) : ℕ) →
      Near (L.lam + fun a => (ν a : ℝ)) lam0 ∧ GapFr D Cgf L.ε (L.lam + fun a => (ν a : ℝ)))
    (γ : Point ℂ (D.R.rS + 1)) (hG : Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0) :
    ENNReal.ofReal ((∏ l, (1 + s l * ‖Dpt γ l‖ ^ 2) ^ N l) ^ 2 *
        ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ ≤
      ENNReal.ofReal ((∏ l, (1 + s l * b ^ (2 * Cb1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) ^ N l) ^ 2 *
        KKc D Cf Cb2 ka b (Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) * jNorm2 L f μsec := by
  classical
  have hka : 0 < ka := hL.2.2.2.2.2.1.2.2.2.1
  set nγ := ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ with hnγ
  set KK := KKc D Cf Cb2 ka b (Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) with hKK
  set Qv := ∏ l, (1 + s l * ‖Dpt γ l‖ ^ 2) ^ N l with hQv
  set B2 := b ^ (2 * Cb1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) with hB2
  set S := ∏ l, (1 + s l * B2) ^ N l with hS
  have hKKpos : 0 < KK := KKc_pos D Cf Cb2 ka b _ hka hb
  have hB2pos : 0 < B2 := Real.rpow_pos_of_pos hb _
  have hSpos : 0 < S := Finset.prod_pos fun l _ => pow_pos (by have := hs l; positivity) _
  have h0N := hNear 0 (by simp only [Pi.zero_apply, Int.cast_zero, abs_zero, Finset.sum_const_zero]; exact Nat.cast_nonneg _)
  have hlam0 : (L.lam + fun a => (((0 : Fin (2 * D.R.rS + D.R.k + 1) → ℤ) a : ℤ) : ℝ)) = L.lam := by
    ext a; simp
  rw [hlam0] at h0N
  have hbase := bp_in_frame D Ch Cg Cgf Cf Cb2 Near hFr hBp L lam0 f μsec ka b hL h0N.1 h0N.2 hf hsec γ hG
  by_cases hn : 0 < nγ
  swap
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_lt.1 hn)), zero_mul]
    exact bot_le
  by_cases htop : jNorm2 L f μsec = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using mul_pos (pow_pos hSpos 2) hKKpos)]
    exact le_top
  by_cases h0 : jNorm2 L f μsec = 0
  · rw [h0, mul_zero] at hbase ⊢
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc, nonpos_iff_eq_zero.1 hbase, mul_zero]
  set J := jNorm2 L f μsec with hJ
  have hJr : 0 < J.toReal := ENNReal.toReal_pos h0 htop
  set c : ℝ := Real.sqrt (J.toReal)⁻¹ with hc
  have hc2 : ‖(c : ℂ)‖ ^ 2 = (J.toReal)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (inv_nonneg.2 hJr.le)]
  have hcJ : ENNReal.ofReal (‖(c : ℂ)‖ ^ 2) = J⁻¹ := by
    rw [hc2, ENNReal.ofReal_inv_of_pos hJr, ENNReal.ofReal_toReal htop]
  have h1 : jNorm2 L (fun x => (c : ℂ) • f x) μsec = 1 := by
    rw [jNorm2_smul, hcJ]
    exact ENNReal.inv_mul_cancel h0 htop
  obtain ⟨Hν, i1, i2, i3, σν, fν, hf0, hfam⟩ := hX L lam0 μsec ka b ka (2 * ∑ l, N l)
    (fun x => (c : ℂ) • f x) (Or.inr rfl) hL1 hR hsec (coef_smul L L.σ c f hf) h1
  have h10 : jNorm2 L (fν 0) μsec = 1 := by rw [hf0]; exact h1
  let I := Fintype.piFinset (fun l : Fin (D.R.rS + 1) => Finset.range (N l + 1))
  have hI : ∀ κ ∈ I, ∑ l, κ l + ∑ l, κ l ≤ 2 * ∑ l, N l := by
    intro κ hκ
    have : ∑ l, κ l ≤ ∑ l, N l := Finset.sum_le_sum fun l _ => by
      have := Fintype.mem_piFinset.1 hκ l
      simp only [Finset.mem_range] at this
      omega
    omega
  have hex := fun (κ : Fin (D.R.rS + 1) → ℕ) (hκ : κ ∈ I) =>
    h92 L lam0 μsec ka b ka _ Hν σν fν (Or.inr rfl) hL1 hR hsec (fun ν hν => (hfam ν hν).2) h10 κ κ (hI κ hκ)
  choose! a ha using hex
  unfold orbSq
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun νm => iSup_le fun hrep => ?_
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrep
  set x := OrbInt L f g νm with hx
  let xν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → (L.Wq →L[ℂ] L.Wp) := fun ν => OrbInt L (fν ν) g νm
  have hx0 : xν 0 = (c : ℂ) • x := by
    show OrbInt L (fν 0) g νm = _
    rw [hf0, OrbInt_smul]
  set M := KK / nγ with hM
  have hM0 : 0 ≤ M := (div_pos hKKpos hn).le
  have hxν : ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      ∑ t, |(ν t : ℝ)| ≤ ((D.R.rS + 1) * (2 * ∑ l, N l) : ℕ) → hsNormSq (xν ν) ≤ M := by
    intro ν hν
    obtain ⟨hHC, hDS, hKF, halt⟩ := hfam ν hν
    let Lν := withRep L _ hHC (Hν ν) (σν ν) hDS
    have hb' := bp_in_frame D Ch Cg Cgf Cf Cb2 Near hFr hBp Lν lam0 (fν ν) μsec ka b hL (hNear ν hν).1
      (hNear ν hν).2 hKF hsec γ hG
    have hle1 : jNorm2 L (fν ν) μsec ≤ 1 := jNorm2_le_one_of_alt D L _ μsec (halt.imp id And.left)
    have hsup : ENNReal.ofReal (hsNormSq (xν ν)) ≤ orbSq Lν (fν ν) γ := by
      unfold orbSq
      exact le_iSup_of_le g <| le_iSup_of_le μR <| le_iSup_of_le νm <| le_iSup_of_le ⟨hr1, hr2, hr3, hr4⟩ le_rfl
    have h3 : ENNReal.ofReal nγ * ENNReal.ofReal (hsNormSq (xν ν)) ≤ ENNReal.ofReal KK :=
      (mul_le_mul' le_rfl hsup).trans (hb'.trans ((mul_le_mul' le_rfl hle1).trans (le_of_eq (mul_one _))))
    rw [← ENNReal.ofReal_mul hn.le, ENNReal.ofReal_le_ofReal_iff hKKpos.le] at h3
    rw [hM, le_div_iff₀ hn, mul_comm]
    exact h3
  let β : (Fin (D.R.rS + 1) → ℕ) → ℝ := fun κ =>
    b ^ (Cb1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, κ l + ∑ l, κ l : ℕ))
  have hβpos : ∀ κ, 0 < β κ := fun κ => Real.rpow_pos_of_pos hb _
  let y : (Fin (D.R.rS + 1) → ℕ) → (L.Wq →L[ℂ] L.Wp) := fun κ => (DpowPt κ γ * star (DpowPt κ γ)) • xν 0
  have hy : ∀ κ ∈ I, hsNormSq (y κ) ≤ β κ ^ 2 * M := by
    intro κ hκ
    obtain ⟨hfin, hsup, hsum, -, horb⟩ := ha κ hκ
    have e := horb hLc hF2 γ g μR νm hG hr1 hr2 hr3 hr4
    have hout : ∀ ν, ν ∉ hfin.toFinset → a κ ν = 0 := fun ν hν => by
      by_contra h
      exact hν (hfin.mem_toFinset.2 h)
    rw [tsum_eq_sum (s := hfin.toFinset) (fun ν hν => by rw [hout ν hν, zero_smul])] at e
    rw [tsum_eq_sum (s := hfin.toFinset) (fun ν hν => by rw [hout ν hν, norm_zero])] at hsum
    have h2 := hs_bound hfin.toFinset (a κ) xν M (fun ν hν => hxν ν
      ((hsup ν (hfin.mem_toFinset.1 hν)).trans (by exact_mod_cast Nat.mul_le_mul_left _ (hI κ hκ))))
    show hsNormSq ((DpowPt κ γ * star (DpowPt κ γ)) • OrbInt L (fν 0) g νm) ≤ _
    rw [e]
    exact h2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg fun ν _ => norm_nonneg _) hsum 2) hM0)
  let cκ : (Fin (D.R.rS + 1) → ℕ) → ℝ := fun κ => ∏ l, ((N l).choose (κ l) : ℝ) * s l ^ κ l
  have hcκ0 : ∀ κ, 0 ≤ cκ κ := fun κ => Finset.prod_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs l) _)
  have hQc : ((Qv : ℝ) : ℂ) = ∑ κ ∈ I, ((cκ κ : ℝ) : ℂ) * (DpowPt κ γ * star (DpowPt κ γ)) := by
    have h := prod_one_add_pow (R := ℂ) (fun l => (s l : ℂ) * (Dpt γ l * star (Dpt γ l))) N
    have e1 : ((Qv : ℝ) : ℂ) = ∏ l, (1 + (s l : ℂ) * (Dpt γ l * star (Dpt γ l))) ^ N l := by
      rw [hQv]
      push_cast
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [e1, h]
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [cκ, DpowPt, star_prod, star_pow, mul_pow, Finset.prod_mul_distrib]
    push_cast
    ring
  have hβ : ∀ κ, β κ = B2 ^ (∑ l, κ l) := by
    intro κ
    show b ^ (Cb1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, κ l + ∑ l, κ l : ℕ)) = _
    rw [hB2, ← Real.rpow_natCast (b ^ (2 * Cb1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) (∑ l, κ l), ← Real.rpow_mul hb.le]
    congr 1
    push_cast
    ring
  have hSc : S = ∑ κ ∈ I, cκ κ * β κ := by
    have h := prod_one_add_pow (R := ℝ) (fun l => s l * B2) N
    rw [hS, h]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [hβ]
    simp only [cκ, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    ring
  have hexp : ((Qv : ℝ) : ℂ) • xν 0 =
      ∑ κ ∈ I, ((cκ κ * β κ : ℝ) : ℂ) • ((((β κ)⁻¹ : ℝ) : ℂ) • y κ) := by
    rw [hQc, Finset.sum_smul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, mul_assoc, mul_inv_cancel₀ (hβpos κ).ne', mul_one, mul_smul]
  have h4 := hs_bound I (fun κ => ((cκ κ * β κ : ℝ) : ℂ)) (fun κ => (((β κ)⁻¹ : ℝ) : ℂ) • y κ) M (by
    intro κ hκ
    rw [hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow]
    rw [inv_mul_le_iff₀ (pow_pos (hβpos κ) 2)]
    exact hy κ hκ)
  rw [← hexp, hsNormSq_smul, hx0, hsNormSq_smul, hc2, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h4
  have h5 : ∑ κ ∈ I, ‖((cκ κ * β κ : ℝ) : ℂ)‖ = S := by
    rw [hSc]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hcκ0 κ) (hβpos κ).le)]
  rw [h5] at h4
  have hreal : Qv ^ 2 * nγ * hsNormSq x ≤ S ^ 2 * KK * J.toReal := by
    calc Qv ^ 2 * nγ * hsNormSq x = (Qv ^ 2 * ((J.toReal)⁻¹ * hsNormSq x)) * (nγ * J.toReal) := by
          field_simp
      _ ≤ (S ^ 2 * M) * (nγ * J.toReal) := mul_le_mul_of_nonneg_right h4 (mul_pos hn hJr).le
      _ = S ^ 2 * KK * J.toReal := by
          rw [hM]; field_simp
  rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hn.le),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hKKpos.le)]
  exact ENNReal.ofReal_le_ofReal hreal

end PieceB3

section PieceB4

theorem blockEnds_prod_le (D : D7) (F G : ℕ → ℝ) (hF0 : ∀ l, 0 ≤ F l) (hFG : ∀ l, F l ≤ G l) (hG1 : ∀ l, 1 ≤ G l)
    (R : ℕ) : ∀ (bs : List (D.host.E × ℕ)) (acc : ℕ), (∀ b ∈ bs, 1 ≤ b.2) → acc + (bs.map Prod.snd).sum = R →
      ((blockEnds D acc bs).map F).prod ≤ ∏ i ∈ Finset.Ico acc R, G (i + 1) := by
  intro bs
  induction bs with
  | nil =>
    intro acc _ hsum
    simp only [List.map_nil, List.sum_nil, add_zero] at hsum
    subst hsum
    simp [blockEnds]
  | cons hd bs ih =>
    intro acc hb hsum
    obtain ⟨e, s⟩ := hd
    have hs1 : 1 ≤ s := hb (e, s) (by simp)
    have hb' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb2 => hb b (by simp [hb2])
    simp only [List.map_cons, List.sum_cons] at hsum
    have hsum' : (acc + s) + (bs.map Prod.snd).sum = R := by omega
    have IH := ih (acc + s) hb' hsum'
    have hR : acc + s ≤ R := by omega
    rw [← Finset.prod_Ico_consecutive _ (by omega : acc ≤ acc + s) hR]
    simp only [blockEnds, List.map_cons, List.prod_cons]
    have hP1 : G (acc + s) ≤ ∏ i ∈ Finset.Ico acc (acc + s), G (i + 1) := by
      obtain ⟨t, ht⟩ : ∃ t, acc + s = t + 1 := ⟨acc + s - 1, by omega⟩
      rw [ht, Finset.prod_Ico_succ_top (by omega : acc ≤ t)]
      have h1 : (1 : ℝ) ≤ ∏ i ∈ Finset.Ico acc t, G (i + 1) := by
        calc (1 : ℝ) = ∏ _i ∈ Finset.Ico acc t, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hG1 _)
      have h2 : 0 ≤ G (t + 1) := le_trans zero_le_one (hG1 _)
      nlinarith
    have hrest0 : 0 ≤ ((blockEnds D (acc + s) bs).map F).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
      exact hF0 l
    have hP10 : 0 ≤ ∏ i ∈ Finset.Ico acc (acc + s), G (i + 1) :=
      Finset.prod_nonneg (fun i _ => le_trans zero_le_one (hG1 _))
    exact mul_le_mul (le_trans (hFG _) hP1) IH hrest0 hP10

section W

variable (D : D7)

def Fl (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (l : Fin (D.R.rS + 1)) : ℝ :=
  1 + absV D v (leadMinorK (ptMat γ) (l.val + 1) (by omega)) ^ 2

theorem Fl_one_le (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (l : Fin (D.R.rS + 1)) : 1 ≤ Fl D v γ l := by
  unfold Fl
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem Fl_last (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) :
    Fl D v γ (Fin.last D.R.rS) = 1 + dLoc D v γ := rfl

theorem wLoc_le (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) : wLoc D v γ ≤ (∏ l, Fl D v γ l) ^ 2 := by
  unfold wLoc
  let G : ℕ → ℝ := fun l => if hl : l ≤ D.R.rS + 1 then (1 + absV D v (leadMinorK (ptMat γ) l hl) ^ 2) ^ 2 else 1
  have hG1 : ∀ l, 1 ≤ G l := by
    intro l
    simp only [G]
    split
    · exact one_le_pow₀ (by nlinarith [sq_nonneg (absV D v (leadMinorK (ptMat γ) l (by assumption)))])
    · exact le_rfl
  have h := blockEnds_prod_le D G G (fun l => zero_le_one.trans (hG1 l)) (fun l => le_rfl) hG1 (D.R.rS + 1) γ.1 0
    (fun b hb => (γ.2.1 b hb).2) (by rw [Nat.zero_add]; exact γ.2.2)
  refine h.trans (le_of_eq ?_)
  rw [← Finset.range_eq_Ico, Finset.prod_range, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [G]
  rw [dif_pos (by omega)]
  rfl

theorem WLoc_le (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1))
    (hG : absV D v (Gglob D T T' γ) ≤ dLoc D v γ) :
    WLoc D T T' v γ ≤ Fl D v γ (Fin.last D.R.rS) * ∏ l, Fl D v γ l := by
  unfold WLoc
  let F : ℕ → ℝ := fun l => if hl : l ≤ D.R.rS + 1 then absV D v (leadMinorK (ptMat γ) l hl) ^ 2 else 1
  let G : ℕ → ℝ := fun l => if hl : l ≤ D.R.rS + 1 then 1 + absV D v (leadMinorK (ptMat γ) l hl) ^ 2 else 1
  have hF0 : ∀ l, 0 ≤ F l := by
    intro l; simp only [F]; split
    · positivity
    · exact zero_le_one
  have hFG : ∀ l, F l ≤ G l := by
    intro l; simp only [F, G]; split
    · linarith
    · exact le_rfl
  have hG1 : ∀ l, 1 ≤ G l := by
    intro l; simp only [G]; split
    · nlinarith [sq_nonneg (absV D v (leadMinorK (ptMat γ) l (by assumption)))]
    · exact le_rfl
  have h := blockEnds_prod_le D F G hF0 hFG hG1 (D.R.rS + 1) γ.1 0
    (fun b hb => (γ.2.1 b hb).2) (by rw [Nat.zero_add]; exact γ.2.2)
  have e : ∏ i ∈ Finset.Ico 0 (D.R.rS + 1), G (i + 1) = ∏ l, Fl D v γ l := by
    rw [← Finset.range_eq_Ico, Finset.prod_range]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [G]
    rw [dif_pos (by omega)]
    rfl
  rw [e] at h
  have hd : dLoc D v γ ≤ Fl D v γ (Fin.last D.R.rS) := by rw [Fl_last]; linarith
  exact mul_le_mul (hG.trans hd) h (List.prod_nonneg (by
    intro a ha
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 ha
    exact hF0 l)) (zero_le_one.trans (Fl_one_le D v γ _))

def NQ (A : ℕ) (p : ℝ) (l : Fin (D.R.rS + 1)) : ℕ :=
  (2 + ⌈p⌉₊) + (if l = Fin.last D.R.rS then (A + 1) / 2 + ⌈p⌉₊ else 0)

theorem sum_NQ (A : ℕ) (p : ℝ) : ∑ l, NQ D A p l = (D.R.rS + 1) * (2 + ⌈p⌉₊) + ((A + 1) / 2 + ⌈p⌉₊) := by
  unfold NQ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.sum_ite_eq']
  simp

theorem weights_arith (Pi0 Ph0 w Wp : ℝ) (A P : ℕ) (hPi1 : 1 ≤ Pi0) (hPh1 : 1 ≤ Ph0) (hw0 : 0 ≤ w)
    (hw : w ≤ Pi0 ^ 2) (hW0 : 0 ≤ Wp) (hWp : Wp ≤ (Ph0 * Pi0) ^ P) :
    w ^ 2 * Ph0 ^ A * Wp ≤ (Pi0 ^ (2 + P) * Ph0 ^ ((A + 1) / 2 + P)) ^ 2 := by
  have hPi0 : 0 ≤ Pi0 := le_trans zero_le_one hPi1
  have hPh0 : 0 ≤ Ph0 := le_trans zero_le_one hPh1
  have hA : A ≤ 2 * ((A + 1) / 2) := by omega
  have e1 : w ^ 2 ≤ Pi0 ^ 4 := by
    calc w ^ 2 = w * w := sq w
      _ ≤ Pi0 ^ 2 * Pi0 ^ 2 := mul_le_mul hw hw hw0 (sq_nonneg _)
      _ = Pi0 ^ 4 := by ring
  have e2 : Ph0 ^ A ≤ Ph0 ^ (2 * ((A + 1) / 2)) := pow_le_pow_right₀ hPh1 hA
  have e3 : Wp ≤ Pi0 ^ (2 * P) * Ph0 ^ (2 * P) := by
    calc Wp ≤ (Ph0 * Pi0) ^ P := hWp
      _ = Pi0 ^ P * Ph0 ^ P := by ring
      _ ≤ Pi0 ^ (2 * P) * Ph0 ^ (2 * P) :=
        mul_le_mul (pow_le_pow_right₀ hPi1 (by omega)) (pow_le_pow_right₀ hPh1 (by omega))
          (pow_nonneg hPh0 _) (pow_nonneg hPi0 _)
  calc w ^ 2 * Ph0 ^ A * Wp ≤ Pi0 ^ 4 * Ph0 ^ (2 * ((A + 1) / 2)) * (Pi0 ^ (2 * P) * Ph0 ^ (2 * P)) :=
        mul_le_mul (mul_le_mul e1 e2 (pow_nonneg hPh0 _) (pow_nonneg hPi0 _)) e3 hW0
          (mul_nonneg (pow_nonneg hPi0 _) (pow_nonneg hPh0 _))
    _ = (Pi0 ^ (2 + P) * Ph0 ^ ((A + 1) / 2 + P)) ^ 2 := by ring

theorem prod_Fl_NQ (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (A : ℕ) (p : ℝ) :
    ∏ l, Fl D v γ l ^ NQ D A p l =
      (∏ l, Fl D v γ l) ^ (2 + ⌈p⌉₊) * Fl D v γ (Fin.last D.R.rS) ^ ((A + 1) / 2 + ⌈p⌉₊) := by
  unfold NQ
  rw [Finset.prod_congr rfl (fun l _ => pow_add (Fl D v γ l) _ _), Finset.prod_mul_distrib, Finset.prod_pow]
  congr 1
  rw [Finset.prod_eq_single (Fin.last D.R.rS)]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem weights_le (T T' : ℕ) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (A : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hG : absV D v (Gglob D T T' γ) ≤ dLoc D v γ) :
    wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * WLoc D T T' v γ ^ p ≤ (∏ l, Fl D v γ l ^ NQ D A p l) ^ 2 := by
  have hw := wLoc_le D v γ
  have hW := WLoc_le D T T' v γ hG
  have hPh1 := Fl_one_le D v γ (Fin.last D.R.rS)
  have hPi1 : (1 : ℝ) ≤ ∏ l, Fl D v γ l := by
    calc (1 : ℝ) = ∏ _l : Fin (D.R.rS + 1), (1 : ℝ) := by simp
      _ ≤ ∏ l, Fl D v γ l := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun l _ => Fl_one_le D v γ l)
  have hw0 : 0 ≤ wLoc D v γ := by
    unfold wLoc
    apply List.prod_nonneg
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    split_ifs <;> positivity
  have hW0 : 0 ≤ WLoc D T T' v γ := by
    unfold WLoc
    apply mul_nonneg (norm_nonneg _)
    apply List.prod_nonneg
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    split_ifs <;> positivity
  have hWp : WLoc D T T' v γ ^ p ≤ (Fl D v γ (Fin.last D.R.rS) * ∏ l, Fl D v γ l) ^ ⌈p⌉₊ := by
    rw [← Real.rpow_natCast]
    calc WLoc D T T' v γ ^ p ≤ (Fl D v γ (Fin.last D.R.rS) * ∏ l, Fl D v γ l) ^ p :=
          Real.rpow_le_rpow hW0 hW hp
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith) (Nat.le_ceil p)
  rw [prod_Fl_NQ, ← Fl_last]
  exact weights_arith _ _ _ _ A ⌈p⌉₊ hPi1 hPh1 hw0 hw (Real.rpow_nonneg hW0 _) hWp

end W

end PieceB4

section PieceB5

section Pw

variable {b : ℝ}

theorem bp_mul (hb : 0 < b) {a c x y : ℝ} (ha : a ≤ b ^ x) (hc : c ≤ b ^ y) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c) :
    a * c ≤ b ^ (x + y) := by
  rw [Real.rpow_add hb]
  exact mul_le_mul ha hc hc0 (ha0.trans ha)

theorem bp_pow (hb : 0 < b) {a x : ℝ} (ha : a ≤ b ^ x) (ha0 : 0 ≤ a) (n : ℕ) : a ^ n ≤ b ^ (x * n) := by
  rw [Real.rpow_mul_natCast hb.le]
  exact pow_le_pow_left₀ ha0 ha n

theorem bp_mono (hb : 1 ≤ b) {x y : ℝ} (h : x ≤ y) : b ^ x ≤ b ^ y := Real.rpow_le_rpow_of_exponent_le hb h

theorem max_inv_mul_le {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    max 1 (1 / (c * x)) ≤ max 1 (1 / c) * max 1 (1 / |x|) := by
  have h1 : (1 : ℝ) ≤ max 1 (1 / c) := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 (1 / |x|) := le_max_left _ _
  have hx' : 0 < |x| := abs_pos.mpr hx
  apply max_le
  · nlinarith
  · calc 1 / (c * x) ≤ 1 / (c * |x|) := by
          rcases lt_or_gt_of_ne hx with h | h
          · have e1 : c * x < 0 := mul_neg_of_pos_of_neg hc h
            have e2 : 1 / (c * x) < 0 := div_neg_of_pos_of_neg one_pos e1
            have e3 : 0 < 1 / (c * |x|) := div_pos one_pos (mul_pos hc hx')
            linarith
          · rw [abs_of_pos h]
      _ = (1 / c) * (1 / |x|) := by rw [one_div_mul_one_div]
      _ ≤ max 1 (1 / c) * max 1 (1 / |x|) :=
        mul_le_mul (le_max_right _ _) (le_max_right _ _) (div_pos one_pos hx').le (by linarith)

end Pw

section Rd

variable (D : D7)

theorem rdE_le (b Ch : ℝ) (hb : 2 ≤ b) (hka : 0 < kaRe D) (hkinv : (kaRe D)⁻¹ ≤ b ^ Ch) :
    D.host.rdE ≤ b ^ (3 + Ch) := by
  have hrd := rdE_pos D
  have hg0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hg1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hgg : (1 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by nlinarith
  have e : (kaRe D)⁻¹ = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * D.host.rdE / (2 * Real.pi) := by
    unfold kaRe Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    have := Real.pi_pos
    field_simp
  have h1 : D.host.rdE ≤ 2 * Real.pi * (kaRe D)⁻¹ := by
    rw [e]
    have hpi := Real.pi_pos
    have : 2 * Real.pi * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * D.host.rdE / (2 * Real.pi)) =
        (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * D.host.rdE := by field_simp
    rw [this]
    nlinarith
  have h2 : 2 * Real.pi ≤ b ^ (3 : ℝ) := by
    have : (2 : ℝ) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
    have h4 := Real.pi_le_four
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    linarith
  exact h1.trans (bp_mul (by linarith) h2 hkinv (by positivity) (inv_nonneg.2 hka.le))

theorem alf_inv_le (Rd : ℝ) (hRd1 : 1 ≤ Rd) (hRd : D.host.rdE ≤ Rd) (i : ℕ) (hi : i ≤ D.R.rS) :
    (alf D i)⁻¹ ≤ Rd ^ D.R.rS := by
  have hrd := rdE_pos D
  have e : (alf D i)⁻¹ = D.host.rdE ^ (D.R.rS - i) := by
    unfold alf
    rw [_root_.zpow_neg, inv_inv, ← zpow_natCast]
    congr 1
    omega
  rw [e]
  exact (pow_le_pow_left₀ hrd.le hRd _).trans (pow_le_pow_right₀ hRd1 (Nat.sub_le _ _))

theorem alfProd_inv_le (Rd : ℝ) (hRd1 : 1 ≤ Rd) (hRd : D.host.rdE ≤ Rd) (n : ℕ) (hn : n ≤ D.R.rS + 1) :
    (((∏ i : Fin n, alf D i) ^ 2) ^ 2)⁻¹ ≤ Rd ^ ((2 * D.R.rS + 2) ^ 2) := by
  have h1 : (∏ i : Fin n, alf D i)⁻¹ ≤ Rd ^ (D.R.rS * n) := by
    rw [← Finset.prod_inv_distrib]
    calc ∏ i : Fin n, (alf D i)⁻¹ ≤ ∏ _i : Fin n, Rd ^ D.R.rS :=
          Finset.prod_le_prod (fun i _ => (inv_pos.2 (alf_pos D i)).le)
            (fun i _ => alf_inv_le D Rd hRd1 hRd i (by have := i.2; omega))
      _ = Rd ^ (D.R.rS * n) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have h0 : 0 ≤ (∏ i : Fin n, alf D i)⁻¹ := inv_nonneg.2 (Finset.prod_nonneg fun i _ => (alf_pos D i).le)
  calc (((∏ i : Fin n, alf D i) ^ 2) ^ 2)⁻¹ = ((∏ i : Fin n, alf D i)⁻¹) ^ 4 := by
        rw [← pow_mul, inv_pow]
    _ ≤ (Rd ^ (D.R.rS * n)) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = Rd ^ (D.R.rS * n * 4) := by rw [← pow_mul]
    _ ≤ Rd ^ ((2 * D.R.rS + 2) ^ 2) := pow_le_pow_right₀ hRd1 (by nlinarith)

end Rd

end PieceB5

section PieceB6

def sQ (D : D7) (l : Fin (D.R.rS + 1)) : ℝ := (((∏ i : Fin (l.val + 1), alf D i) ^ 2) ^ 2)⁻¹

theorem sQ_nonneg (D : D7) (l : Fin (D.R.rS + 1)) : 0 ≤ sQ D l := by
  unfold sQ
  positivity

def EQ (D : D7) (Ch Cf Cb1 Cb2 : ℝ) (SN : ℕ) : ℝ :=
  2 * ((4 + Ch + 2 * Cb1) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * SN) + 2 * Ch * Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 +
    Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 +
    (3 + 3 * Ch) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)

theorem alfProd_inv_le_b (D : D7) (Ch b : ℝ) (hCh : 0 ≤ Ch) (hb : 2 ≤ b) (hka : 0 < kaRe D)
    (hk2 : (kaRe D)⁻¹ ≤ b ^ Ch) (n : ℕ) (hn : n ≤ D.R.rS + 1) :
    (((∏ i : Fin n, alf D i) ^ 2) ^ 2)⁻¹ ≤ b ^ ((3 + Ch) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hRd := rdE_le D b Ch hb hka hk2
  have hRd1 : (1 : ℝ) ≤ b ^ (3 + Ch) := Real.one_le_rpow (by linarith) (by linarith)
  have h := alfProd_inv_le D (b ^ (3 + Ch)) hRd1 hRd n hn
  calc _ ≤ (b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2) := h
    _ = b ^ ((3 + Ch) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
        push_cast
        try ring

theorem FrC_nonneg (D : D7) (Cf ka : ℝ) (hka : 0 < ka) : 0 ≤ FrC D Cf ka := by
  unfold FrC
  positivity

theorem num_Fr (D : D7) (Ch Cf b ka : ℝ) (hCh : 0 ≤ Ch) (hCf : 0 ≤ Cf) (hb : 2 ≤ b) (hka : 0 < ka)
    (hk1 : ka ≤ b ^ Ch) (hk2 : ka⁻¹ ≤ b ^ Ch) :
    FrC D Cf ka ≤ b ^ (2 * Ch * Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) := by
  unfold FrC
  have hb0 : 0 < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set m : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hrm : (D.R.rS : ℝ) ≤ m := by
    rw [hm]; push_cast; linarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
  have M1 : max ka⁻¹ (ka⁻¹)⁻¹ ≤ b ^ Ch := by
    rw [inv_inv]; exact max_le hk2 hk1
  have M2 : max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ≤ b ^ (Ch * (D.R.rS : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le]
    apply max_le
    · exact pow_le_pow_left₀ hka.le hk1 _
    · rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.mpr hka.le) hk2 _
  have P1 : max ka⁻¹ (ka⁻¹)⁻¹ ^ (Cf * m ^ 2) ≤ b ^ (Ch * (Cf * m ^ 2)) := by
    rw [Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow (le_max_of_le_left (inv_nonneg.mpr hka.le)) M1 (by positivity)
  have P2 : max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ^ (Cf * m) ≤ b ^ (Ch * (D.R.rS : ℝ) * (Cf * m)) := by
    rw [Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow (le_max_of_le_left (pow_nonneg hka.le _)) M2 (by positivity)
  calc _ ≤ b ^ (Ch * (Cf * m ^ 2)) * b ^ (Ch * (D.R.rS : ℝ) * (Cf * m)) :=
        mul_le_mul P1 P2 (by positivity) (by positivity)
    _ = b ^ (Ch * (Cf * m ^ 2) + Ch * (D.R.rS : ℝ) * (Cf * m)) := (Real.rpow_add hb0 _ _).symm
    _ ≤ b ^ (2 * Ch * Cf * m ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have : Ch * Cf * ((D.R.rS : ℝ) * m) ≤ Ch * Cf * (m * m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrm hm0) (mul_nonneg hCh hCf)
        nlinarith

theorem GsC_pos (D : D7) (ka : ℝ) (hka : 0 < ka) : 0 < GsC D ka := by
  unfold GsC
  positivity

theorem num_Gs (D : D7) (Ch b ka : ℝ) (hCh : 0 ≤ Ch) (hb : 2 ≤ b) (hka : 0 < ka)
    (hk1 : ka ≤ b ^ Ch) (hk2 : ka⁻¹ ≤ b ^ Ch) :
    (GsC D ka)⁻¹ ≤ b ^ (2 * Ch * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) := by
  have hGs : GsC D ka = ka ^ (2 * D.R.rS * (D.R.rS + 1)) := by
    unfold GsC
    rw [inv_pow, ← pow_mul]
    field_simp
    ring
  have hb1 : (1 : ℝ) ≤ b := by linarith
  rw [hGs, ← inv_pow]
  calc (ka⁻¹) ^ (2 * D.R.rS * (D.R.rS + 1)) ≤ (b ^ Ch) ^ (2 * D.R.rS * (D.R.rS + 1)) :=
        pow_le_pow_left₀ (inv_nonneg.mpr hka.le) hk2 _
    _ = b ^ (Ch * ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ)) := by
        rw [Real.rpow_mul_natCast (by linarith)]
    _ ≤ b ^ (2 * Ch * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have e : ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ) ≤ 2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 := by
          push_cast
          nlinarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
        have e2 := mul_le_mul_of_nonneg_left e hCh
        linarith

theorem num_G (D : D7) (Ch Cb2 b : ℝ) (hCh : 0 ≤ Ch) (hCb2 : 0 ≤ Cb2) (hb : 2 ≤ b) (hka : 0 < kaRe D)
    (hk1 : kaRe D ≤ b ^ Ch) (hk2 : (kaRe D)⁻¹ ≤ b ^ Ch) (A : ℕ)
    (hA : Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ A) (x : ℝ) (hx : x ≠ 0) :
    max 1 (1 / (GsC D (kaRe D) * (((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 * x))) ^
        (Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) ≤
      b ^ ((3 + 3 * Ch) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) *
        max 1 (1 / |x|) ^ A := by
  have hb0 : 0 < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set m : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hm
  set P4 : ℝ := ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 with hP4
  set E : ℝ := Cb2 * m ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hGs := GsC_pos D (kaRe D) hka
  have hM2 : (1 : ℝ) ≤ max 1 (1 / |x|) := le_max_left _ _
  have hX0 : 0 ≤ (3 + 3 * Ch) * m ^ 2 := by positivity
  have hB1 : (1 : ℝ) ≤ b ^ ((3 + 3 * Ch) * m ^ 2 * E) := Real.one_le_rpow hb1 (mul_nonneg hX0 hE0)
  have hM2A : max 1 (1 / |x|) ^ E ≤ max 1 (1 / |x|) ^ A := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hM2 hA
  rcases (show 0 ≤ P4 by rw [hP4]; positivity).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_mul, mul_zero, div_zero, max_eq_left zero_le_one, Real.one_rpow]
    exact one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hM2)
  · have hc : 0 < GsC D (kaRe D) * P4 := mul_pos hGs hpos
    have key := max_inv_mul_le hc hx
    rw [mul_assoc] at key
    have hinv : 1 / (GsC D (kaRe D) * P4) ≤ b ^ ((3 + 3 * Ch) * m ^ 2) := by
      have g1 := num_Gs D Ch b (kaRe D) hCh hb hka hk1 hk2
      have g2 := alfProd_inv_le_b D Ch b hCh hb hka hk2 D.R.rS (by omega)
      rw [one_div, mul_inv]
      calc (GsC D (kaRe D))⁻¹ * P4⁻¹ ≤ b ^ (2 * Ch * m ^ 2) * b ^ ((3 + Ch) * m ^ 2) :=
            mul_le_mul g1 g2 (inv_nonneg.mpr hpos.le) (Real.rpow_nonneg hb0.le _)
        _ = b ^ ((3 + 3 * Ch) * m ^ 2) := by
            rw [← Real.rpow_add hb0]
            congr 1
            ring
    have hM1 : max 1 (1 / (GsC D (kaRe D) * P4)) ≤ b ^ ((3 + 3 * Ch) * m ^ 2) :=
      max_le (Real.one_le_rpow hb1 hX0) hinv
    have hM10 : (0 : ℝ) ≤ max 1 (1 / (GsC D (kaRe D) * P4)) := le_trans zero_le_one (le_max_left _ _)
    calc max 1 (1 / (GsC D (kaRe D) * (P4 * x))) ^ E
        ≤ (max 1 (1 / (GsC D (kaRe D) * P4)) * max 1 (1 / |x|)) ^ E :=
          Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) key hE0
      _ = max 1 (1 / (GsC D (kaRe D) * P4)) ^ E * max 1 (1 / |x|) ^ E :=
          Real.mul_rpow hM10 (le_trans zero_le_one hM2)
      _ ≤ (b ^ ((3 + 3 * Ch) * m ^ 2)) ^ E * max 1 (1 / |x|) ^ A :=
          mul_le_mul (Real.rpow_le_rpow hM10 hM1 hE0) hM2A
            (Real.rpow_nonneg (le_trans zero_le_one hM2) _)
            (Real.rpow_nonneg (Real.rpow_nonneg hb0.le _) _)
      _ = b ^ ((3 + 3 * Ch) * m ^ 2 * E) * max 1 (1 / |x|) ^ A := by
          rw [← Real.rpow_mul hb0.le]

end PieceB6

section PieceB7

def RangeOne (D : D7) (Ch Cg Cg1 Cq Cgf dist : ℝ)
    (Near : (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → (Fin (2 * D.R.rS + D.R.k + 1) → ℝ) → Prop)
    (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (A : ℕ) (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X → ∀ v,
    BesselRangeNearParameter D Cg1 Cq (X.L v) (lamSH D.R (D.hc v)) (2 * ∑ l, NQ D A p l) ∧
    ((D.R.rS + 1 : ℕ) : ℝ) * (l1 (X.L v).lam (lamSH D.R (D.hc v)) + (((D.R.rS + 1) * (2 * ∑ l, NQ D A p l) : ℕ) : ℝ)) ≤
      hNC (X.L v).ε (lamSH D.R (D.hc v)) / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      ∑ t, |(ν t : ℝ)| ≤ ((D.R.rS + 1) * (2 * ∑ l, NQ D A p l) : ℕ) →
      Near ((X.L v).lam + fun a => (ν a : ℝ)) (lamSH D.R (D.hc v)) ∧
        GapFr D Cgf (X.L v).ε ((X.L v).lam + fun a => (ν a : ℝ))

theorem Fl_eq (D : D7) (v : D.what₂.Tau) (γ : Point D.host.E (D.R.rS + 1)) (l : Fin (D.R.rS + 1)) :
    1 + sQ D l * ‖Dpt (ptLoc D v γ) l‖ ^ 2 = Fl D v γ l := by
  unfold Dpt Fl sQ absV
  rw [leadMinor_loc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← mul_assoc]
  have hpos : 0 < ((∏ i : Fin (l.val + 1), alf D i) ^ 2) ^ 2 := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin (l.val + 1)) _ => alf_pos D i)
    positivity
  rw [inv_mul_cancel₀ hpos.ne', one_mul]

theorem Dpt_norm_turnPt {r : ℕ} (p : Point ℂ (r + 1)) (l : Fin (r + 1)) :
    ‖Dpt (Pv.Frames.turnPt p) l‖ = ‖Dpt p l‖ := by
  have h := Pv.Frames.leadMinor_turnPt p (l.val + 1) (by omega)
  unfold Dpt
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

end PieceB7

section PieceB8

def AQ (D : D7) (Cb2 : ℝ) : ℕ := ⌈Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2⌉₊

theorem AQ_ge (D : D7) (Cb2 : ℝ) : Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ AQ D Cb2 := by
  unfold AQ
  exact Nat.le_ceil _

theorem AQ_half_le (D : D7) (Cb2 : ℝ) (h : 0 ≤ Cb2) :
    (((AQ D Cb2 + 1) / 2 : ℕ) : ℝ) ≤ Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 + 1 := by
  have h1 : (AQ D Cb2 + 1) / 2 ≤ AQ D Cb2 := by omega
  have h2 : (AQ D Cb2 : ℝ) < Cb2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 + 1 := by
    unfold AQ
    exact Nat.ceil_lt_add_one (mul_nonneg h (sq_nonneg _))
  calc (((AQ D Cb2 + 1) / 2 : ℕ) : ℝ) ≤ (AQ D Cb2 : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2.le

theorem sum_weighted_point_counts_le_cube (D : D7) (Aw Cb2 : ℝ) (hAw : 0 ≤ Aw) (h : 0 ≤ Cb2) :
    ((∑ l, NQ D (AQ D Cb2) (Aw * ((D.R.rS : ℝ) + 1) ^ 2) l : ℕ) : ℝ) ≤
      (1 + Aw + Cb2) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by
  rw [sum_NQ]
  have h1 := AQ_half_le D Cb2 h
  have hp : 0 ≤ Aw * ((D.R.rS : ℝ) + 1) ^ 2 := mul_nonneg hAw (sq_nonneg _)
  have hc := (Nat.ceil_lt_add_one hp).le
  push_cast
  push_cast at h1
  have ht : (1 : ℝ) ≤ (D.R.rS : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
  have ht0 : (0 : ℝ) ≤ (D.R.rS : ℝ) + 1 := by linarith
  have f1 := mul_le_mul_of_nonneg_left hc ht0
  have t2 : ((D.R.rS : ℝ) + 1) ^ 2 ≤ ((D.R.rS : ℝ) + 1) ^ 3 := pow_le_pow_right₀ ht (by norm_num)
  have t1 : ((D.R.rS : ℝ) + 1) ≤ ((D.R.rS : ℝ) + 1) ^ 3 := by nlinarith
  have f2 := mul_le_mul_of_nonneg_left t2 hAw
  have f3 := mul_le_mul_of_nonneg_left t2 h
  have f4 : 0 ≤ Aw * ((D.R.rS : ℝ) + 1) ^ 3 := mul_nonneg hAw (pow_nonneg ht0 _)
  have f5 : 0 ≤ Cb2 * ((D.R.rS : ℝ) + 1) ^ 3 := mul_nonneg h (pow_nonneg ht0 _)
  linarith

def firstBoundConstant (Ch Cf Cb1 Cb2 : ℝ) : ℝ :=
  2 * (4 + Ch + 2 * Cb1) * (Cb2 + 1) + 2 * Ch * Cf + Cb2 + (3 + 3 * Ch) * Cb2

def weightedBoundConstant (Aw Ch Cf Cb1 Cb2 : ℝ) : ℝ :=
  2 * (4 + Ch + 2 * Cb1) * (1 + Aw + Cb2) + 2 * Ch * Cf + Cb2 + (3 + 3 * Ch) * Cb2

end PieceB8

section PieceB9

section Gen

variable {n : ℕ}

end Gen

theorem epsSH_both (D : D7) : ∃ a b : Fin (2 * D.R.rS + D.R.k + 1), epsSH D.R a ≠ epsSH D.R b := by
  have hk := Ranks.k_ge D.R
  refine ⟨⟨0, by omega⟩, ⟨D.R.k, by omega⟩, ?_⟩
  have h1 : epsSH D.R ⟨0, by omega⟩ = true := by
    unfold epsSH epsS
    simp only [Fin.val_cast]
    rw [if_pos (by omega)]
  have h2 : epsSH D.R ⟨D.R.k, by omega⟩ = false := by
    unfold epsSH epsS
    simp only [Fin.val_cast]
    rw [if_neg (by omega)]
    have : D.R.k - (D.R.k - 1) = 1 := by omega
    simp [this]
  rw [h1, h2]
  exact Bool.noConfusion

def XX (D : D7) : ℝ :=
  ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)

def NearG (D : D7) (ρ γ₀ : ℝ) (lam' lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) : Prop :=
  l1 lam' lam0 ≤ ρ ∧ AllGaps lam0 γ₀

end PieceB9

section PieceB10

def rhoQ (D : D7) (A : ℕ) (p : ℝ) : ℝ := (((D.R.rS + 1) * (2 * ∑ l, NQ D A p l) : ℕ) : ℝ)

def NumRange (D : D7) (Cg Cg1 Cq Cgf dist γ₀ : ℝ) (A : ℕ) (p : ℝ) : Prop :=
  Cg1 * ((2 * ∑ l, NQ D A p l : ℕ) : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ≤ γ₀ ∧
  dist + (((D.R.rS + 1) * (2 * ∑ l, NQ D A p l + D.R.rS + 2) : ℕ) : ℝ) ≤
    min (max (Cg * XX D) γ₀ / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ))) γ₀ / Cq ∧
  dist + rhoQ D A p ≤ max (Cg * XX D) γ₀ - Cgf * XX D ∧
  ((D.R.rS + 1 : ℕ) : ℝ) * (dist + rhoQ D A p) ≤ max (Cg * XX D) γ₀ / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ))

structure InB (D : D7) (Ch Cg Cg1 Cq Cgf Cf Cb1 Cb2 : ℝ) : Prop where
  hCh : 0 ≤ Ch
  hCf : 0 ≤ Cf
  hCb1 : 0 ≤ Cb1
  hCb2 : 0 ≤ Cb2
  hCg : 2 ≤ Cg
  hCg1 : Cg1 ≤ Cg
  hCq : 0 < Cq
  fr : FrameBesselBound D Cgf Cf
  p92 : BesselConjugatesEveryCell D Ch Cg1 Cq Cb1
  fam : ExFamC D Ch Cg1 Cq

theorem lam_eq_of_dist0 (D : D7) {Ch Cg : ℝ} {T T' : ℕ} {b : ℝ} (X : BData D Ch Cg T T' b 0) (v : D.what₂.Tau) :
    (X.L v).lam = lamSH D.R (D.hc v) := by
  have h := X.hnear v
  unfold l1 at h
  funext a
  have h0 : |(X.L v).lam a - lamSH D.R (D.hc v) a| ≤ 0 :=
    le_trans (Finset.single_le_sum (f := fun a => |(X.L v).lam a - lamSH D.R (D.hc v) a|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ a)) h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

end PieceB10

section PieceB11

end PieceB11

section PieceB12

structure WeightedBoundOpenInputs (D : D7) (Ch Aw Cu Cg Cg1 Cq Cg' C1 Cs CA CQ Cb Cb1 Cb2 Cgf1 Cf : ℝ) : Prop where
  bp : TheoremBPrimePointwise D Ch Cg Cb
  ubp : UniformityTheoremBPrime D Ch Cu Cg Cg' Cb
  p90P : PieriNormPairing D Ch Cg Cq
  p91 : BesselLeadingMinorBound D Ch Cg Cq Cb
  p92c : BesselIterationNearParameter D Ch Cg Cq Cb
  fr : FrameBesselBound D Cgf1 Cf
  lit : LitFormalDegree
  fam : ExFamC D Ch Cg1 Cq
  shell : ShellSmooth D
  exp : OneStepCellExpansion D Ch Cg1 Cq Cb1
  bp1 : BpAll D Ch Cg Cb2 (NearG D (0 + rhoQ D (AQ D Cb2) 0) (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3))
  bp3 : BpAll D Ch Cg Cb2 (NearG D (0 + rhoQ D (AQ D Cb2) (Aw * ((D.R.rS : ℝ) + 1) ^ 2))
    (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4))
  besselBoundUnitaryFirst : BpAll D Ch Cg Cb2 (NearG D (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 + rhoQ D (AQ D Cb2) 0)
    (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3))
  besselBoundUnitaryThird : BpAll D Ch Cg Cb2 (NearG D (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 +
                         rhoQ D (AQ D Cb2) (Aw * ((D.R.rS : ℝ) + 1) ^ 2))
    (max (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)))
  pieri : PieriShellBound D Ch Cg Cq C1 CA CQ
  rep : DerivedActionPhaseBound D Ch Cg Cq Cs
  lowK : LowestKTypeRightInvariant D Ch Cg
  jMeas : JMeas D
  phMeas : PhMeas D
  nilpotentFrameMatrix : NumRange D Cg Cg1 Cq Cgf1 (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)
    (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (AQ D Cb2) 0
  unitaryRangeCubic : NumRange D Cg Cg1 Cq Cgf1 (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)
    (max (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) (AQ D Cb2)
    (Aw * ((D.R.rS : ℝ) + 1) ^ 2)

structure WeightedBoundConstants (Ch Aw Cg Cg1 Cq C1 CardSubmodulesOfIndexLePow C2 Cs CA CQ Cb Cb1 Cb2 Cgf1 Cgf Cf : ℝ) : Prop where
  hCh : 0 ≤ Ch
  hAw : 0 ≤ Aw
  hCf : 0 ≤ Cf
  hCb1 : 0 ≤ Cb1
  hCb2 : 0 ≤ Cb2
  hCg : 2 ≤ Cg
  gap_constant_nonneg : 0 ≤ Cg1
  hCg1 : Cg1 ≤ Cg
  hCq : 1 ≤ Cq
  hCb1b : Cb1 ≤ Cb
  hCK4 : firstBoundConstant Ch Cf Cb1 Cb2 ≤ Cb - 6
  hCK5 : weightedBoundConstant Aw Ch Cf Cb1 Cb2 ≤ Cb - 6
  r1 : 2 * (1 + Aw + Cb2) * Cg1 ≤ Cg
  r2 : (2 + Aw + Cb2) * Cq ^ 2 ≤ Cg
  r3 : 1 + Aw + Cb2 ≤ Cg - Cgf1
  hCgf : Cgf1 ≤ Cgf
  hCs : 0 ≤ Cs
  hC1 : 1 ≤ C1
  twice_smooth_le_first : 2 * Cs ≤ C1
  hCA : 0 ≤ CA
  hCQ : 1 ≤ CQ
  constant_log_relation : 1 + 2 * |Ch| + CA + 3 * (Real.logb 2 CQ + 2) ≤ 2 * CardSubmodulesOfIndexLePow
  hC2 : CardSubmodulesOfIndexLePow + (Real.logb 2 C1 + 4 + |Ch|) ≤ C2

end PieceB12

end Formalism.MainNotions.TheoremBConstants
