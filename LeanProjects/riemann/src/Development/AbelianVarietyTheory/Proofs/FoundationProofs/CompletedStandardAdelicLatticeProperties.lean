import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.CompletedLattice

variable (D : D7)

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  rw [← h2]
  exact (h1 1).1

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ}
    {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ z') : z = z' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D τ (z i j) = δ * embT D τ (z' i j) := congrFun (congrFun (congrFun h τ) i) j
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem exists_mul_IhE_mem (cc : Ideal (𝓞 D.host.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Ideal.absNorm D.host.𝔟, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, -, a, ha, s, hs, rfl⟩ := hy
    rw [FractionalIdeal.mem_coe] at ha
    unfold Host.AA0 at ha
    rw [FractionalIdeal.mem_inv_iff hB] at ha
    have h1 := ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.absNorm_mem D.host.𝔟))
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [map_natCast] at hr
    have h2 : inc D (r : D.host.E) ∈ OhE D := (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩
    have h3 : inc D ((c : D.host.K) : D.host.E) ∈ OhE D :=
      (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩
    have h4 : (Ideal.absNorm D.host.𝔟 : AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        inc D ((c : D.host.K) : D.host.E) * (inc D (r : D.host.E) * s) := by
      have : (r : D.host.E) = a * (Ideal.absNorm D.host.𝔟 : D.host.E) := hr
      rw [this, map_mul, map_mul, map_natCast]
      ring
    rw [h4]
    exact mul_mem h3 (mul_mem h2 hs)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  intro D hg cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hn : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hA hB
  refine ⟨fun z => ⟨fun h => hB z h, fun h => ?_⟩, fun x hx => ?_, fun ζ m hm => ?_, fun ζ => ?_,
    exists_mul_IhE_mem D cc, _, hn, GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc⟩
  · obtain ⟨z', h1, h2⟩ := hA _ h
    rw [pt_injective D cc hδ h1]
    exact h2
  · obtain ⟨z, h1, -⟩ := hA x hx
    exact ⟨z, h1⟩
  · choose e t ht h using fun (i : Fin N') (j : Fin N) => (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc).1 (ζ i j) m hm
    refine ⟨Matrix.of e, Matrix.of t, ht, ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, Matrix.of_apply, ← h]
    ring
  · choose n hn0 h using fun k : Fin N' × Fin N => GlobalTheory.AdelicApprox.exists_denom D (ζ k.1 k.2)
    refine ⟨Ideal.absNorm cc * ∏ k, n k, Nat.mul_pos hn (Finset.prod_pos fun k _ => hn0 k), fun i j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
    have h1 := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc _ (mul_mem (natCast_mem (OhE D) c) (h (i, j)))
    rw [Matrix.smul_apply, nsmul_eq_mul, hc]
    convert h1 using 1
    push_cast
    ring

end GlobalTheory.CompletedLattice
