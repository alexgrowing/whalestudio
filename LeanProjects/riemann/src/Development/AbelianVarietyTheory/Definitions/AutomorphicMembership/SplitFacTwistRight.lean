import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.ThModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem nonempty_tow (D : D7) : Nonempty (Tow D) := GlobalTheory.Mem.Th.nonempty_tow (GlobalTheory.WittLow.wittLowEx D)

theorem orthEx (D : D7) : OrthEx D := by
  intro V hV
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (two_ne_zero : (2 : D.host.E) ≠ 0) V.rank V.hT.flip
    (fun x y => V.herm.eq y x) V.rank_eq
  have ho : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0 := fun i j hij => hb j i hij.symm
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.FockBasisMatrix.basis_matrix D V).2 b
  have hd : ∀ τ, ((V.frame.toMatrix b).map (tauE D τ)).det ≠ 0 := fun τ => by
    have := (tauE D τ).map_det (V.frame.toMatrix b)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (h1.map (tauE D τ)).ne_zero
  choose A hA hA' using fun τ => GlobalTheory.MonomialDiag.exists_monomial _ _ _ (gramAt D V τ) _ _ (hV (tauE D τ)) (hd τ)
    (h3 ho τ).1 (h3 ho τ).2.1
  exact ⟨A, V.frame.toMatrix b, hA, h1, fun i j hij => (h2 i j).trans (ho i j hij), hA'⟩

theorem nonempty_orthDec (D : D7) : Nonempty (OrthDec D) := GlobalTheory.Mem.Th.nonempty_orthDec (orthEx D)

theorem om_rational {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χ χ' : IdC D}
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (h : IsWeilOn ψ V W χ χ' om)
    {γ : GA D V} (hγ : γ ∈ GQ V) {δ : GA D W} (hδ : δ ∈ GQ W) (Φ Φ' : ThS ψ V W) (w : WA V W)
    (e : Φ'.1 = Heisenberg₂ ψ V W w Φ.1) : (om (γ, δ) Φ).1 (actHom V W γ δ w) = Φ.1 w := by
  have h0 : ∀ u : WA V W, symplH V W 0 u = 0 := fun u => by
    simp [symplH, sympl, hHom]
  have h1 := congrFun (h.Heisenberg₂ γ δ w Φ Φ' e) 0
  rw [h.aut γ hγ δ hδ, e] at h1
  simpa [Heisenberg₂, h0] using h1.symm

theorem root_of_at {e d : AE D} (hd : d * cA D d = 1)
    (hs : (e + cA D e) * (d - 1) = d - 1) :
    e * d + (1 - e) = d * cA D (e * d + (1 - e)) := by
  rw [map_add, map_mul, map_sub, map_one]
  have h1 : d * (cA D e * cA D d + (1 - cA D e)) = cA D e * (d * cA D d) + d - d * cA D e := by ring
  rw [h1, hd]
  linear_combination hs

theorem splitFac_twist_right {V W : HSp D} (h : V.rank ≠ W.rank) (χ χ' ν : IdC D) (x y : (AE D)ˣ) :
    splitFac V W χ (χ' * ν) x y = (if V.rank < W.rank then (ν x)⁻¹ else ν x) * splitFac V W χ χ' x y := by
  unfold splitFac
  by_cases k : V.rank < W.rank
  · rw [if_pos k.le, if_pos k.le, if_pos k, MonoidHom.mul_apply, _root_.mul_inv_rev, mul_assoc]
  · have k' : ¬ V.rank ≤ W.rank := by omega
    rw [if_neg k', if_neg k', if_neg k, MonoidHom.mul_apply, mul_comm (χ' x), mul_assoc]

theorem splitFac_twist_left {V W : HSp D} (h : V.rank ≠ W.rank) (χ χ' ν : IdC D) (x y : (AE D)ˣ) :
    splitFac V W (χ * ν) χ' x y = (if V.rank < W.rank then ν y else (ν y)⁻¹) * splitFac V W χ χ' x y := by
  unfold splitFac
  by_cases k : V.rank < W.rank
  · rw [if_pos k.le, if_pos k.le, if_pos k, MonoidHom.mul_apply, mul_comm (χ y), mul_left_comm]
  · have k' : ¬ V.rank ≤ W.rank := by omega
    rw [if_neg k', if_neg k', if_neg k, MonoidHom.mul_apply, _root_.mul_inv_rev, mul_left_comm]

end GlobalTheory.Mem.ThModel

end
