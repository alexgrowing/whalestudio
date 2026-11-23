import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQuaStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

variable {D : D7}

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ x₃ τ) • f := by
  intro D ψ θ S T χS χT om hW hθ _ _ sT hS hT a b ha hb x₁ x₂ x₃ h1 h2 h3 f hf hv g hg h hh hc
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := exists_root hθ T (fun τ => hdet (hT τ)) h hh
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (sT τ) (hT τ).1
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) sT hS hT g hg h hh
    (fun τ => by rw [one_mul, mul_one]) hc x y hx hy f hf hv]
  congr 1
  have hb' : ∀ τ, ((-x₃ τ - p τ : ℤ) : ℚ) = b τ - T.rank / 2 := fun τ => by
    have := h3 τ
    rw [hp] at this
    apply Rat.cast_injective (α := ℂ)
    push_cast
    linear_combination -this
  rw [Circle.coe_mul, Circle.coe_inv,
    hxv _ (fun τ => -x₃ τ - p τ) (fun τ => by rw [hb']; exact hasInfExp_twist (hb τ) (e2 τ) _),
    hyv _ x₂ (fun τ => by rw [h2]; exact hasInfExp_twist (ha τ) (e2 τ) _),
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨d1, d2⟩ := hd τ (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h)) (hc τ)
  have inv : ∀ (V : HSp D) (k : GA D V),
      (compAt θ τ (Formalism.L2.Theta.mt V k)).det * (compAt θ τ (Formalism.L2.Theta.mt V k⁻¹)).det = 1 := fun V k => by
    rw [det_compAt, det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one (inv S g)
  have h0 := left_ne_zero_of_mul_eq_one (inv T h)
  rw [d2] at h0
  have h0' := left_ne_zero_of_mul h0
  have e : x₁ τ = x₂ τ + S.rank := by
    have : (x₁ τ : ℚ) = x₂ τ + S.rank := by rw [h1, h2]; ring
    exact_mod_cast this
  have alg : ∀ (A B G : ℂ) (u v : ℤ) (n k : ℕ), A ≠ 0 → G ≠ 0 →
      (G ^ (-v - k))⁻¹ * (A * B) ^ u * (A ^ n * G⁻¹ ^ k) = A ^ (u + n) * B ^ u * G ^ v := by
    intro A B G u v n k hA hG
    rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hG, _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    have := zpow_ne_zero v hG
    have := pow_ne_zero k hG
    field_simp
  rw [d1, d2, eq_inv_of_mul_eq_one_right (inv S g), e]
  exact alg _ _ _ _ _ _ _ h0' g0

end GlobalTheory.VacuumCharacter

end
