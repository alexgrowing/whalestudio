import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaStab

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  exact h2 ▸ (h1 1).1

theorem mem_standardThetaLattice_iff_adelicIdeal (hcc : cc ≠ ⊥) (x : VC D N N') : x ∈ La0 D (tor0 D cc δ) N N' ↔
    ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, inc D (z i j) ∈ IhE D cc := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hx
    obtain ⟨z, hz, h⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') x hx
    exact ⟨z, hz, fun i j => by simpa using h i j⟩
  · rintro ⟨z, rfl, h⟩
    exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') z (fun i j => by simpa using h i j)

theorem inc_mem_of_isIntegral {e : D.host.E} (he : IsIntegral ℤ e) : inc D e ∈ OhE D :=
  GlobalTheory.NormSum.MovedTheta.inc_int (⟨e, he⟩ : 𝓞 D.host.E)

theorem mulV_mem (hcc : cc ≠ ⊥) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (h' : ∀ i j, IsIntegral ℤ (M' i j)) (h : ∀ i j, IsIntegral ℤ (M i j)) (x : VC D N N')
    (hx : x ∈ La0 D (tor0 D cc δ) N N') : mulV D M' M x ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
  refine (mem_standardThetaLattice_iff_adelicIdeal hcc _).2 ⟨_, mulV_pt D cc δ M' M z, fun i j => ?_⟩
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun k _ => ?_
  rw [mul_comm]
  refine MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h k j)) (sum_mem fun l _ => ?_)
  exact MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h' i l)) (hz l k)

theorem exists_denom {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, IsIntegral ℤ ((m • M) i j) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h (M i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, ← natCast_zsmul]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h1
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', neg_smul]; exact h1.neg

theorem mulV_nsmul (m' m : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (x : VC D N N') : mulV D (m' • M') (m • M) x = (m' * m) • mulV D M' M x := by
  funext τ
  have e : ∀ {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) D.host.E),
      (k • A).map (embT D τ) = k • A.map (embT D τ) := by
    intro n k A
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
  change (m' • M').map (embT D τ) * Matrix.of (x τ) * (m • M).map (embT D τ) =
    (m' * m) • (M'.map (embT D τ) * Matrix.of (x τ) * M.map (embT D τ))
  rw [e, e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, mul_smul]

theorem inv_eq_adj {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    (((g : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = (adj D γ).map (inc D) := by
  have h1 : γ * adj D γ = 1 := (GlobalTheory.NormSum.mem_ratG_intG D n).2.2.2.1 g γ h
  apply Units.inv_eq_of_mul_eq_one_right
  unfold IsRat at h
  rw [h, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_iff_moved (hcc : cc ≠ ⊥) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : IsRat D (γA : GL (Fin N) (AE D)) γ)
    (h' : IsRat D (γA' : GL (Fin N') (AE D)) γ') (hL : Moves D (γA : GL (Fin N) (AE D)) L₁)
    (hL' : Moves D (γA' : GL (Fin N') (AE D)) L₁') (x : VC D N N') :
    x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have h1 : adj D γ * γ = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ h)
  have h1' : adj D γ' * γ' = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' h')
  have key : ∀ z : Matrix (Fin N') (Fin N) D.host.E,
      (((γA' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = (adj D γ' * z * γ).map (inc D) := by
    intro z
    have h2 := h
    unfold IsRat at h2
    rw [inv_eq_adj h', h2, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro hx
    obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
    rw [mulV_pt]
    refine GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' γA γA' _ _ hL hL' _ fun i j => ?_
    have e : adj D γ' * (γ' * z * adj D γ) * γ = z := by
      rw [Matrix.mul_assoc γ', ← Matrix.mul_assoc (adj D γ'), h1', Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rw [key, e]
    exact hz i j
  · intro hx
    obtain ⟨w, hw, hz⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' γA γA' _ _ hL hL' _ hx
    refine (mem_standardThetaLattice_iff_adelicIdeal hcc x).2 ⟨adj D γ' * w * γ, ?_, fun i j => ?_⟩
    · rw [← mulV_pt, ← hw, mulV_mulV, h1, h1', mulV_one]
    · have := hz i j
      rw [key] at this
      exact this

end GlobalTheory.ThetaStab

open GlobalTheory.ThetaStab in

theorem GlobalTheory.ThetaStab.mulV_theta_lattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  refine ⟨fun M' M h' h x hx => mulV_mem hcc M' M h' h x hx, fun M' M => ?_,
    fun γA γA' γ γ' L₁ L₁' h h' hL hL' x => mem_iff_moved hcc γA γA' γ γ' L₁ L₁' h h' hL hL' x⟩
  obtain ⟨m', hm', h'⟩ := exists_denom M'
  obtain ⟨m, hm, h⟩ := exists_denom M
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun x hx => ?_⟩
  rw [← mulV_nsmul]
  exact mulV_mem hcc _ _ h' h x hx
