import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.FlagUnipotentLattices.ThirdHeightFromSecond

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ}

theorem unitary_group_mul_mem {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem cayley_conj_mem_diagonal_model {ε : Fin (2 * r + k + 1) → Bool} {P a : Mat k r} (hP : IsCayleyU k r ε P)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

theorem discrete_series_map_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hrep := hDS.2.2.1.1.2 _ (cayley_conj_mem_diagonal_model hP ha).1 _ (cayley_conj_mem_diagonal_model hP hb).1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have e1 : P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = a * b := by
    calc P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = a * b := by rw [h1]; simp
  simp only [e1, (cayley_conj_mem_diagonal_model hP ha).2, (cayley_conj_mem_diagonal_model hP hb).2] at hrep
  exact hrep

end Grp

theorem rank_height_ranges (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k) (hG : GapBig k r b) :
    ∃ h : ℝ, LowGapGe h r b ∧
      120 * (rk48 k r : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h ∧
      16 * (((rk48 k r ^ 2 / 2 + 1 : ℕ) : ℝ)) * Real.sqrt ((r : ℝ) + 1) + 16 * ((rk48 k r : ℝ) - 1) * ((r : ℝ) + 1) < h ∧
      16 * (rk48 k r : ℝ) ^ 2 * Real.sqrt ((r : ℝ) + 1) ≤ h := by
  obtain ⟨t, -, ht, -, hgap⟩ := hG
  set n : ℕ := rk48 k r with hn
  have hn2 : 2 ≤ n := by simp only [hn, rk48]; omega
  have hq : ((r : ℝ) + 1) ≤ (n : ℝ) / 2 := by
    have : 2 * (r + 1) ≤ n := by simp only [hn, rk48]; omega
    have h' : ((2 * (r + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  obtain ⟨e1, e2, e3⟩ := Formalism.HermitianLatticeCounting.Final.S8.explicitC n ((r : ℝ) + 1)
    (2 * ((n + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3) hn2 (by positivity) hq
  have hM : 3 * (n : ℝ) ≤ ((n + (2 * r + 2) * t : ℕ) : ℝ) := by
    have : 3 * n ≤ n + (2 * r + 2) * t := by nlinarith
    exact_mod_cast this
  have hM3 : (3 * (n : ℝ)) ^ 3 ≤ ((n + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hM 3
  have hbig : 43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ 2 * ((n + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
    nlinarith
  obtain ⟨f1, f2, f3⟩ := e3 hbig
  refine ⟨2 * ((n + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3, fun j hj => (hgap j hj).le, f1, ?_, f3⟩
  linarith

structure BData : Type 1 where
  k : ℕ
  r : ℕ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  v : Fin (k - 1) → ℝ
  b : Fin (2 * r + 2) → ℝ
  H : Type
  [hN : NormedAddCommGroup H]
  [hI : InnerProductSpace ℂ H]
  [hC : CompleteSpace H]
  σ : Mat k r → (H →L[ℂ] H)
  Vp : Type
  [vN : NormedAddCommGroup Vp]
  [vI : InnerProductSpace ℂ Vp]
  [vF : FiniteDimensional ℂ Vp]
  π : Mat k r → (Vp →L[ℂ] Vp)
  w : H
  μG : Measure (Formalism.QuantumDeterminants.Mt k r)
  μS : Measure (Formalism.QuantumDeterminants.Mt k r)
  ν : Measure (Formalism.QuantumDeterminants.Mt k r)

attribute [instance] BData.hN BData.hI BData.hC BData.vN BData.vI BData.vF

namespace BData

variable (X : BData)

abbrev G : Set (Mat X.k X.r) := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk X.k X.r)

abbrev ψ : Mat X.k X.r → ℂ := psiGen X.k X.r X.z X.c

abbrev e : Mat X.k X.r → ℂ := eFun X.μG X.σ X.w

def Hyp : Prop :=
  RealPlaceNumericalSetting X.k X.r X.z X.c X.u X.v X.b ∧ IsDSHpk X.k X.r (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) X.σ ∧
    IsHCTypeW X.k X.r X.z X.u X.π ∧ IsLowUnitH X.k X.r (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) X.σ X.w ∧
    IsHaarOn X.G X.μG ∧ IsHaarOn (Formalism.QuantumDeterminants.Sset X.k X.r X.z) X.μS ∧ IsQuotMeas X.μG X.μS X.ν

def IsSol (W : Mat X.k X.r → X.Vp) : Prop :=
  AEStronglyMeasurable (fun x => W (Matrix.of x)) X.μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) X.ν ∧
    IsSPsiEquiv X.z X.ψ X.π W ∧ l2SG X.ν W < ⊤ ∧ l2SG X.ν W ≠ 0 ∧
    ∀ x ∈ X.G, rconv X.μG X.e W x = W x

def IsFun (B : X.H → X.Vp) : Prop :=
  IsBesselMapSm X.z X.ψ X.σ X.π B ∧ HasOrdLe X.k X.r (rk48 X.k X.r ^ 2 / 2 + 1) X.σ B ∧
    ∃ x ∈ smoothVecs (k := X.k) (r := X.r) X.σ, B x ≠ 0

def W' (B : X.H → X.Vp) : Mat X.k X.r → X.Vp := fun g => B (X.σ g X.w)

def Φ (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Mat X.k X.r → X.Vp := fun g => (χ g : ℂ) • X.W' B g

def Wf (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Mat X.k X.r → X.Vp := rconv X.μG X.e (X.Φ B χ)

def OrbitSmooth : Prop := ∀ g ∈ X.G, X.σ g X.w ∈ smoothVecs (k := X.k) (r := X.r) X.σ

def OrbitNZ (B : X.H → X.Vp) : Prop := ∃ g ∈ X.G, B (X.σ g X.w) ≠ 0

def IsCut (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) : Prop :=
  (∀ g, 0 ≤ χ g) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset X.k X.r X.z, ∀ g ∈ X.G, χ (s * g) = χ g) ∧
    AEStronglyMeasurable (fun x => X.Φ B χ (Matrix.of x)) X.μG ∧ (∃ M : ℝ, ∀ g ∈ X.G, ‖X.Φ B χ g‖ ≤ M) ∧
    ((∫⁻ x, (‖X.Φ B χ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂X.ν) < ⊤ ∧
      ∃ Ω : Set (Mat X.k X.r), IsCompact Ω ∧
        ∀ g ∈ X.G, χ g ≠ 0 → ∃ s ∈ Formalism.QuantumDeterminants.Sset X.k X.r X.z, s * g ∈ Ω) ∧
    0 < ∫ x, χ (Matrix.of x) * ‖X.W' B (Matrix.of x)‖ ^ 2 ∂X.ν

def CutStep (B : X.H → X.Vp) : Prop := X.OrbitNZ B → ∃ χ, X.IsCut B χ

def ConvolutionKernelIntegrable : Prop := Integrable (fun x => X.e (Matrix.of x)) X.μG

def IdemStep (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ → ∀ x ∈ X.G, rconv X.μG X.e (X.Wf B χ) x = X.Wf B χ x

def ProjectionSquareIntegrable (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ → AEStronglyMeasurable (fun x => X.Wf B χ (Matrix.of x)) X.μG ∧
    AEStronglyMeasurable (fun x => X.Wf B χ (Matrix.of x)) X.ν ∧ l2SG X.ν (X.Wf B χ) < ⊤

def Pairing (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ →
    ∫ x, ⟪X.W' B (Matrix.of x), X.Wf B χ (Matrix.of x)⟫_ℂ ∂X.ν =
      ∫ x, ⟪X.W' B (Matrix.of x), (χ (Matrix.of x) : ℂ) • X.W' B (Matrix.of x)⟫_ℂ ∂X.ν

variable {X}

theorem W'_equiv (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hs : X.OrbitSmooth) :
    IsSPsiEquiv X.z X.ψ X.π (X.W' B) := by
  intro h hh m hm g hg
  have hhm : h * m ∈ X.G := unitary_group_mul_mem hh.1 hm.1
  unfold W'
  rw [discrete_series_map_mul hX.2.1 hhm hg]
  exact hB.1.2.2.1 h hh m hm _ (hs g hg)

theorem Φ_equiv (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hs : X.OrbitSmooth) {χ : Mat X.k X.r → ℝ}
    (hχ : X.IsCut B χ) : IsSPsiEquiv X.z X.ψ X.π (X.Φ B χ) := by
  intro h hh m hm g hg
  unfold Φ
  rw [hχ.2.1 (h * m) ⟨h, hh, m, hm, rfl⟩ g hg, W'_equiv hX hB hs h hh m hm g hg, map_smul, smul_comm]

theorem mp_left (hX : X.Hyp) {g : Mat X.k X.r} (hg : g ∈ X.G) :
    MeasurePreserving (Formalism.QuantumDeterminants.lmulM g) X.μG X.μG := by
  refine ⟨?_, hX.2.2.2.2.1.2.2.2 g hg⟩
  unfold Formalism.QuantumDeterminants.lmulM
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h0 : Measurable fun x : Formalism.QuantumDeterminants.Mt X.k X.r => x l j := by fun_prop
  exact h0.const_mul _

theorem ae_mem (hX : X.Hyp) : ∀ᵐ y ∂X.μG, Matrix.of y ∈ X.G := by
  have := hX.2.2.2.2.1.2.2.1
  rw [ae_iff]
  exact this

theorem integrable_conv (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) (he : X.ConvolutionKernelIntegrable)
    {g : Mat X.k X.r} (hg : g ∈ X.G) :
    Integrable (fun y => X.e (Matrix.of y) • X.Φ B χ (g * Matrix.of y)) X.μG := by
  obtain ⟨M, hM⟩ := hχ.2.2.2.1
  have hm : AEStronglyMeasurable (fun y => X.Φ B χ (g * Matrix.of y)) X.μG :=
    hχ.2.2.1.comp_measurePreserving (mp_left hX hg)
  refine he.smul_bdd M hm ?_
  filter_upwards [ae_mem hX] with y hy
  exact hM _ (unitary_group_mul_mem hg hy)

theorem Wf_equiv (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hs : X.OrbitSmooth) {χ : Mat X.k X.r → ℝ}
    (hχ : X.IsCut B χ) (he : X.ConvolutionKernelIntegrable) : IsSPsiEquiv X.z X.ψ X.π (X.Wf B χ) := by
  intro h hh m hm g hg
  unfold Wf rconv
  have h1 : ∀ᵐ y ∂X.μG, X.e (Matrix.of y) • X.Φ B χ (h * m * g * Matrix.of y) =
      X.ψ m • X.π h (X.e (Matrix.of y) • X.Φ B χ (g * Matrix.of y)) := by
    filter_upwards [ae_mem hX] with y hy
    rw [Matrix.mul_assoc (h * m) g, Φ_equiv hX hB hs hχ h hh m hm _ (unitary_group_mul_mem hg hy), map_smul, smul_comm]
  rw [integral_congr_ae h1, integral_smul, ContinuousLinearMap.integral_comp_comm _ (integrable_conv hX hχ he hg)]

theorem Wf_ne_zero {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ)
    (hm : AEStronglyMeasurable (fun x => X.Wf B χ (Matrix.of x)) X.ν) (hp : X.Pairing B) : l2SG X.ν (X.Wf B χ) ≠ 0 := by
  have key := Formalism.HermitianLatticeCounting.Final.S8.assemblyB (Formalism.QuantumDeterminants.Mt X.k X.r) X.ν X.Vp (fun _ x => X.Wf B χ (Matrix.of x))
    (fun x => χ (Matrix.of x)) (fun x => X.W' B (Matrix.of x)) (hp χ hχ) hχ.2.2.2.2.2
  intro h0
  apply key
  unfold l2SG at h0
  have hme : AEMeasurable (fun x => (‖X.Wf B χ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) X.ν := (hm.enorm).pow_const 2
  have := (lintegral_eq_zero_iff' hme).1 h0
  filter_upwards [this] with x hx
  simpa using hx

theorem exists_sol' (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (s1 : X.OrbitSmooth) (s2 : X.OrbitNZ B)
    (s3 : X.CutStep B) (s4 : X.ConvolutionKernelIntegrable) (s5 : X.IdemStep B) (s6 : X.ProjectionSquareIntegrable B) (s7 : X.Pairing B) : ∃ W, X.IsSol W := by
  obtain ⟨χ, hχ⟩ := s3 s2
  obtain ⟨m1, m2, hfin⟩ := s6 χ hχ
  exact ⟨X.Wf B χ, m1, m2, Wf_equiv hX hB s1 hχ s4, hfin, Wf_ne_zero hχ m2 s7, s5 χ hχ⟩

end BData

theorem bessel_existence_iff_solutions (D : Formalism.BasicNotions.D7) (C : ℝ) :
    Conclusion2 D C ↔ ∀ X : BData, X.Hyp → GapC C X.k X.r X.b → ∃ W, X.IsSol W := by
  constructor
  · intro h X hX hC
    exact h X.k X.r X.z X.c X.u X.v X.b hX.1 hC X.H X.σ hX.2.1 X.Vp X.π hX.2.2.1 X.w hX.2.2.2.1 X.μG X.μS X.ν
      hX.2.2.2.2.1 hX.2.2.2.2.2.1 hX.2.2.2.2.2.2
  · intro h k r z c u v b hS hC H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hS' hQ
    exact h { k := k, r := r, z := z, c := c, u := u, v := v, b := b, H := H, σ := σ, Vp := Vp, π := π, w := w,
              μG := μG, μS := μS, ν := ν } ⟨hS, hσ, hπ, hw, hG, hS', hQ⟩ hC

def BesselExistenceFacts : Prop :=
  ∀ X : BData, X.Hyp → ∀ B : X.H → X.Vp, X.IsFun B →
    X.OrbitSmooth ∧ X.OrbitNZ B ∧ X.CutStep B ∧ X.ConvolutionKernelIntegrable ∧ X.IdemStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Pairing B

theorem bessel_existence_of_ordered (D : Formalism.BasicNotions.D7) (C : ℝ) (ha : FunctionalContinuityOrder D C) (hS : BesselExistenceFacts) : Conclusion2 D C := by
  rw [bessel_existence_iff_solutions]
  intro X hX hC
  obtain ⟨B, b1, b2, b3⟩ := ha X.k X.r X.z X.c X.u X.v X.b hX.1 hC X.H X.σ hX.2.1 X.Vp X.π hX.2.2.1
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hS X hX B ⟨b1, b2, b3⟩
  exact BData.exists_sol' hX ⟨b1, b2, b3⟩ s1 s2 s3 s4 s5 s6 s7

theorem bessel_existence_of_facts (D : Formalism.BasicNotions.D7) (C : ℝ) (hS : FunctionalContinuityOrder D C → adm2 D → adm6 D → BesselExistenceFacts) : HodgeTateFromSandwich D C :=
  fun ha h2 h6 => bessel_existence_of_ordered D C ha (hS ha h2 h6)

theorem bessel_existence_uniform_of_facts (hS : ∀ (D : Formalism.BasicNotions.D7) (C : ℝ), FunctionalContinuityOrder D C → adm2 D → adm6 D → BesselExistenceFacts) : ClosedFormProjectorBound :=
  ⟨0, fun C _ D => bessel_existence_of_facts D C (hS D C)⟩

theorem family_bessel_existence {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) (h : ∀ D : Formalism.BasicNotions.D7, HodgeTateFromSandwich D C) : DeterminantValueFamily Fm C :=
  fun ha h2 h6 x i => h (Fm.D x i) (ha x i) (h2 x i) (h6 x i)

end Formalism.MainNotions.LeviCoordinates

end
