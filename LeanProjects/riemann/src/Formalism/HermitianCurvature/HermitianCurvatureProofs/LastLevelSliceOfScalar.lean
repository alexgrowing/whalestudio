import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

lemma castW_mul (a b : B.Mat k 0) : castW (a * b) = castW a * castW b := by
  unfold castW
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]

lemma castW_ct (a : B.Mat k 0) : (castW a)ᴴ = castW aᴴ := by
  unfold castW
  simp

lemma hb_eq : Hb k = castW (Hpk k 0) := by
  ext i j
  simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Matrix.diagonal_apply, Hpk]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i = Fin.last k
    · subst hl
      simp [Fin.last]
    · have hv : (i : ℕ) ≠ k := fun h => hl (Fin.ext (by simpa [Fin.last] using h))
      have hlt : (i : ℕ) < k + 1 := i.isLt
      simp [hl, hv]
      omega
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hij, Fin.ext_iff, hv]

lemma castW_mem {μ : B.Mat k 0} (hμ : μ ∈ GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by
  have h : μᴴ * Hpk k 0 * μ = Hpk k 0 := hμ
  rw [hb_eq, castW_ct, ← castW_mul, ← castW_mul, h]

def NNSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m → ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        B.gN ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN)

def Slice1 : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)

def SliceRegularityClauses : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O

theorem last_level_slice_of_parts : Slice1 → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := by
  intro h1 h23 k r Wp Wq _ _ _ _ _ _ D A m F hThr hF
  exact ⟨h1 k r Wp Wq D A m F hThr hF, (h23 k r Wp Wq D A m F hThr hF).1, (h23 k r Wp Wq D A m F hThr hF).2⟩

theorem slice1_of_nnSlice : NNSlice → Slice1 := by
  intro hS k r Wp Wq _ _ _ _ _ _ D A m F hThr hF c hc μ hμ
  obtain ⟨ν, hν⟩ := hF
  have hx : bigCell k r c (castW μ) ∈ GV k r := big_cell_mem_holds k r c (castW μ) hc (castW_mem hμ)
  have := B5.haar_sigmaFinite D.haarN
  have hae : ∀ᵐ nn ∂(D.μN.prod D.μN), (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (B5.haar_ae D.haarN)).and
      (Measure.quasiMeasurePreserving_snd.ae (B5.haar_ae D.haarN))
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} := B6.isClosed_Nset k r
  have hTc : IsClosed {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)
  have h1c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r) := continuous_fst
  have h2c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.2 : Mat k r) := continuous_snd
  have hy : ContinuousOn (fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    B6.continuousOn_matrix_mul (B6.continuousOn_matrix_mul
      ((B6.inv_continuousOn k r).comp h1c.continuousOn (fun nn h => B6.Nset_sub _ _ h.1)) continuousOn_const)
      h2c.continuousOn
  have hyG : ∀ nn ∈ {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r},
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2 ∈ GV k r := fun nn h =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B6.Nset_sub _ _ h.1)) hx) (B6.Nset_sub _ _ h.2)
  have hcomp := (B6.continuousOn_of_contDiffOn_group hν.1).comp hy hyG
  have hmeas : AEStronglyMeasurable
      (fun nn : Mt k r × Mt k r => F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2))
      (D.μN.prod D.μN) := by
    have := hcomp.aestronglyMeasurable (μ := D.μN.prod D.μN) hTc.measurableSet
    have hr : (D.μN.prod D.μN).restrict
        {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} =
        D.μN.prod D.μN := Measure.restrict_eq_self_of_ae_mem hae
    rwa [hr] at this
  refine Integrable.mono' ((hS k r Wp Wq D A m hThr c hc μ hμ).const_mul ν) hmeas ?_
  filter_upwards [hae] with nn hnn
  have hyg := hyG nn hnn
  have hpos : 0 < gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) := B6.gN_pos hyg
  have hb := hν.2 [] [] (by simp) (by simp) (by simp) _ hyg
  change gN _ ^ A * ‖F _‖ ≤ ν at hb
  rw [Real.rpow_neg hpos.le]
  rw [mul_comm, ← le_div_iff₀ (Real.rpow_pos_of_pos hpos A)] at hb
  calc _ ≤ _ := hb
    _ = _ := by rw [div_eq_mul_inv]

theorem _root_.Formalism.FourierDecayAlt.P.last_level_slice_of_scalar : NNSlice → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := fun h h23 =>
  last_level_slice_of_parts (slice1_of_nnSlice h) h23

end Formalism.FourierDecayAlt.P.JFxDs5
