import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.ClosedExistsOfCompact

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem rst_iff {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r z z') (hpos : PosPt k r z z' γ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : g ∈ Rst k r z z' γ ↔ g ∈ RStab k r γ := by
  have hγu : IsUnit γ.det := uh_isUnit hpos.1
  rw [(Formalism.FourierDecayAlt.P.stabilizer_split k r z z' γ hstd hpos).2.1]
  constructor
  · rintro ⟨hg, n, hn, rfl⟩
    refine ⟨hg, ?_⟩
    have : γ⁻¹ * (γ * n * γ⁻¹) * γ = n := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγu, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hγu, Matrix.one_mul]
    rw [this]; exact hn
  · rintro ⟨hg, hg'⟩
    refine ⟨hg, _, hg', ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul]

theorem et_equiv (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hstd : Std k r L.z L.z') (hpos : PosPt k r L.z L.z' γ) (hmono : IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ)) (T : ℝ) :
    ∃ ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, ∀ n : Mt k r,
      Matrix.of n ∈ Nset k r → ρh n ∈ RStab k r γ ∧
      ∀ a : Mt k r, Matrix.of a ∈ RStab k r γ →
        ((fun i j => (Matrix.of a * Matrix.of n) i j : Mt k r) ∈ ET (k := k) (r := r) L.z L.z' γ T ↔
          Formalism.FourierDecayAlt.B.rmulF (ρh n) a ∈ AT (k := k) (r := r) γ T) := by
  classical
  have hSD := Formalism.FourierDecayAlt.P.c2_section_decomp k r L.z L.z' γ hstd hpos hmono
  have hRg := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) (uh_isUnit hpos.1)
  let ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun n =>
    if h : Matrix.of n ∈ Sset k r L.z then (hSD (Matrix.of n) h).exists.choose.1 else 1
  refine ⟨ρh, fun n hn => ?_⟩
  have hnS : Matrix.of n ∈ Sset k r L.z := n_in_sset L.z hn
  have hspec := (hSD (Matrix.of n) hnS).exists.choose_spec
  have hρdef : ρh n = (hSD (Matrix.of n) hnS).exists.choose.1 := dif_pos hnS
  set ρ0 := (hSD (Matrix.of n) hnS).exists.choose.1 with hρ0
  set σ0 := (hSD (Matrix.of n) hnS).exists.choose.2 with hσ0
  have hρ0R : ρ0 ∈ RStab k r γ := (rst_iff hstd hpos ρ0).1 hspec.1
  have hσ0 : σ0 ∈ Sg k r L.z L.z' γ := hspec.2.1
  have hn0 : Matrix.of n = ρ0 * σ0 := hspec.2.2
  rw [hρdef]
  refine ⟨hρ0R, fun a ha => ?_⟩
  have haU : IsUnit (Matrix.of a).det := uh_isUnit ha.1.1
  have hρU : IsUnit ρ0.det := uh_isUnit hρ0R.1.1
  have haρ : Matrix.of a * ρ0 ∈ RStab k r γ := hRg.mul_mem _ ha _ hρ0R
  have hanS : Matrix.of a * Matrix.of n ∈ Sset k r L.z := n_in_sset L.z (WeylGroupFacts.mem_n_mul ha.1 hn)
  have hsg := sg_eq (k := k) (r := r) L.z L.z' hstd.2.1 γ
  constructor
  · rintro ⟨y, hy, hΦ⟩
    have hyU : Matrix.of y ∈ UH (Hpk k r) := hy.1.1.1
    rw [uh_inv_eq hyU] at hΦ
    have hΦ' : (Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n) ∈ Sg k r L.z L.z' γ := by rw [hsg]; exact hΦ
    have hyu : IsUnit (Matrix.of y).det := uh_isUnit hyU
    have e1 : Matrix.of a * Matrix.of n = Matrix.of y * ((Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n)) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mul]
    have e2 : Matrix.of a * Matrix.of n = (Matrix.of a * ρ0) * σ0 := by rw [hn0, Matrix.mul_assoc]
    have huniq := (hSD _ hanS).unique
      (y₁ := (Matrix.of y, (Matrix.of y)⁻¹ * (Matrix.of a * Matrix.of n)))
      (y₂ := (Matrix.of a * ρ0, σ0))
      ⟨(rst_iff hstd hpos _).2 hy.1, hΦ', e1⟩ ⟨(rst_iff hstd hpos _).2 haρ, hσ0, e2⟩
    have hyeq : Matrix.of y = Matrix.of a * ρ0 := congrArg Prod.fst huniq
    have : Formalism.FourierDecayAlt.B.rmulF ρ0 a = y := by
      show (Matrix.of a * ρ0 : Matrix _ _ ℂ) = Matrix.of y
      rw [hyeq]
    rw [this]; exact hy
  · intro hy
    refine ⟨_, hy, ?_⟩
    have hyM : Matrix.of (Formalism.FourierDecayAlt.B.rmulF ρ0 a) = Matrix.of a * ρ0 := rfl
    rw [hyM, uh_inv_eq haρ.1.1, ← hsg, Matrix.mul_inv_rev]
    show ρ0⁻¹ * (Matrix.of a)⁻¹ * (Matrix.of a * Matrix.of n) ∈ Sg k r L.z L.z' γ
    have : ρ0⁻¹ * (Matrix.of a)⁻¹ * (Matrix.of a * Matrix.of n) = σ0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of a)⁻¹, Matrix.nonsing_inv_mul _ haU, Matrix.one_mul,
        hn0, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρU, Matrix.one_mul]
    rw [this]; exact hσ0

theorem at_pos {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)}
    (hR0 : μR ≠ 0) (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0) : ∃ T : ℕ, μR (AT (k := k) (r := r) γ T) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hU : μR {x : Mt k r | Matrix.of x ∈ RStab k r γ} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (measure_iUnion_null hcon)
    obtain ⟨T, hT⟩ := exists_nat_ge (Formalism.FourierDecayAlt.B.gN (Matrix.of y))
    exact Set.mem_iUnion.2 ⟨T, hy, hT⟩
  have : μR Set.univ = 0 := by
    refine measure_mono_null (fun y _ => ?_) (measure_union_null hU hRc)
    by_cases h : Matrix.of y ∈ RStab k r γ
    · exact Or.inl h
    · exact Or.inr h
  exact hR0 (Measure.measure_univ_eq_zero.mp this)

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
