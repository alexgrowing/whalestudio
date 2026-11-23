import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem minpoly_units_conj {F A : Type*} [Field F] [Ring A] [Algebra F A] (u : Aˣ) (x : A) :
    minpoly F ((u : A) * x * ((u⁻¹ : Aˣ) : A)) = minpoly F x := by
  let e : A ≃ₐ[F] A :=
    { toFun := fun z => (u : A) * z * ((u⁻¹ : Aˣ) : A)
      invFun := fun z => ((u⁻¹ : Aˣ) : A) * z * u
      left_inv := fun z => by simp [mul_assoc]
      right_inv := fun z => by simp [mul_assoc]
      map_mul' := fun z w => by simp [mul_assoc]
      map_add' := fun z w => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : A) * algebraMap F A r * ((u⁻¹ : Aˣ) : A) = algebraMap F A r
        rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  exact minpoly.algEquiv_eq e x

theorem fixL_smul_iff {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) : FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm d c z] at hd
    exact smul_right_injective _ hc hd
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [Matrix.mulVec_smul, hd, smul_comm]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

theorem rep_smul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (η : grp G β)
    (l : PLv G v β) : ∃ c : ℂ, c ≠ 0 ∧
      Projectivization.rep ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
        c • ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
          Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))) := by
  set w := Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))
  have hw : w ≠ 0 := Projectivization.rep_nonzero _
  have hMw : (toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w ≠ 0 := by
    intro h0
    apply hw
    apply toV_injective G v β η
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]
  have hl : ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw := by
    show Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = _
    conv_lhs => rw [← Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))]
    rw [Projectivization.map_mk]
    simp only [Matrix.toLin'_apply]
    rfl
  rw [hl]
  have h2 := Projectivization.mk_rep (Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw)
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hMw).1 h2
  exact ⟨c, c.ne_zero, by rw [← hc, Units.smul_def]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

end GlobalTheory.CxUnfold
