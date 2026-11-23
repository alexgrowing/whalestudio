import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.IntegralRankOneProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem inPair_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) : InPair L (stabAct γ a p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨h1, WeylGroupFacts.mem_n_mul ha.1 h2, h3, WeylGroupFacts.mem_n_mul ha.2 h4⟩

theorem inPair_of_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (hp : InPair L (stabAct γ a p)) : InPair L p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have key : ∀ b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, b ∈ Nset k r →
      ∀ m : Mt k r, b * of m ∈ Nset k r → of m ∈ Nset k r := by
    intro b hb m hm
    have hu : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
    have : of m = b⁻¹ * (b * of m) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]
    exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hb) hm
  exact ⟨h1, key a ha.1 _ h2, h3, key _ ha.2 _ h4⟩

private theorem psi_mul_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psi k r z c (g * h) = psi k r z c g * psi k r z c h := by
  unfold psi
  rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff _).1 hg).2 ((WeylGroupFacts.nset_iff _).1 hh).2, mul_add,
    Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem psi_mul_star_psi_eq_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  have h : ‖psi k r z c g‖ = 1 := by
    unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [show star (psi k r z c g) = (starRingEnd ℂ) (psi k r z c g) from rfl, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h]
  simp

theorem Psi_stab (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (x : Mt k r) :
    Psi L w0 v v' ξ ξ' γ (stabAct γ a p) x =
      Psi L w0 v v' ξ ξ' γ p (Matrix.of.symm (γ⁻¹ * a⁻¹ * γ * Matrix.of x)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hγu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (of fun i j => M i j) = M :=
    fun M => rfl
  rw [Psi_eq, Psi_eq]
  simp only [stabAct, e, Equiv.apply_symm_apply]
  have m1 : (of p.1.1)⁻¹ * (a * of p.1.2)⁻¹ * γ * of x =
      (of p.1.1)⁻¹ * (of p.1.2)⁻¹ * γ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ γ⁻¹, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul]
  have m2 : (of p.2.1)⁻¹ * (γ⁻¹ * a * γ * of p.2.2)⁻¹ * of x =
      (of p.2.1)⁻¹ * (of p.2.2)⁻¹ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hγu]
    simp only [Matrix.mul_assoc]
  have hc : psi k r L.z L.c (a * of p.1.2) * star (psi k r L.z' L.c (γ⁻¹ * a * γ * of p.2.2)) =
      psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2)) := by
    rw [psi_mul_of_mem_Nset L.z L.hz.1 L.c ha.1 h2, psi_mul_of_mem_Nset L.z' L.hz'.1 L.c ha.2 h4, star_mul',
      hrel a ha]
    calc psi k r L.z' L.c (γ⁻¹ * a * γ) * psi k r L.z L.c (of p.1.2) *
          (star (psi k r L.z' L.c (γ⁻¹ * a * γ)) * star (psi k r L.z' L.c (of p.2.2)))
        = (psi k r L.z' L.c (γ⁻¹ * a * γ) * star (psi k r L.z' L.c (γ⁻¹ * a * γ))) *
          (psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2))) := by ring
      _ = _ := by rw [psi_mul_star_psi_eq_one, one_mul]
  rw [m1, m2, hc]

end Formalism.MainNotions.S.Pv.AmpDDPf
