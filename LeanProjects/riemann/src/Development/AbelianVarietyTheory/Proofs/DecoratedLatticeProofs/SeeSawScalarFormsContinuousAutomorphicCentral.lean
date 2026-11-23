import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
