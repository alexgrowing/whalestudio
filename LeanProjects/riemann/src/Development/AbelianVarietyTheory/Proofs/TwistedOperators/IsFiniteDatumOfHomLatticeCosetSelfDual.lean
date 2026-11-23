import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFinVecOfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
open GlobalTheory.Grid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

theorem absNorm_mem_idS (I : Ideal (𝓞 D.host.E)) :
    ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
  have : oToS D.host.F D.host.E ((Ideal.absNorm I : ℕ) : 𝓞 D.host.E) ∈ idS D.host.F I :=
    Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  simpa using this

theorem mk_eq_of_eq_add {A : Type} [CommRing A] {R : Subring A} (J : Ideal R) {x y w : A} (hx : x ∈ R) (hy : y ∈ R)
    (hw : w ∈ R) {n : ℕ} (hn : (n : R) ∈ J) (h : x = y + n * w) :
    Ideal.Quotient.mk J ⟨x, hx⟩ = Ideal.Quotient.mk J ⟨y, hy⟩ := by
  rw [Ideal.Quotient.eq]
  have e : (⟨x, hx⟩ - ⟨y, hy⟩ : R) = (n : R) * ⟨w, hw⟩ := by
    apply Subtype.ext
    change x - y = ((n : R) : A) * w
    rw [h]
    push_cast
    ring
  rw [e]
  exact J.mul_mem_right _ hn

open Classical in

theorem isFinVec_of_isCosetVec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ}
    (hv : GlobalTheory.Grid.IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    (hI : I ≠ ⊥) (hc : GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f) : GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  let φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ := fun y =>
    if (∀ i j, ∃ h : y i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Ideal.Quotient.mk (idS D.host.F I) ⟨y i j, h⟩ = cmpS D.host.F I (c i j)) then 1 else 0
  have hfun : cosetInd S T e I c = fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0 := by
    funext x
    unfold cosetInd
    by_cases hx : IsHalf e x
    · rw [if_pos hx]
      by_cases hx' : InCosetOf S T I c x
      · rw [if_pos ⟨hx, hx'⟩]
        exact (if_pos hx').symm
      · rw [if_neg fun h => hx' h.2]
        exact (if_neg hx').symm
    · rw [if_neg hx, if_neg fun h => hx h.1]
  have hS' := GlobalTheory.FlipPath.isSelfDualC_sgn ε hS
  refine GlobalTheory.FlipPath.isFinVec_of_own hv hS hT he (φ := φ) ⟨?_, ?_⟩
  · rw [← hfun]
    obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := sgn ε S.V) hS'.1.fg hT.1.fg S.β T.β
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := sgn ε S.V) hS'.1 hT.1 S.β T.β
    have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
    have hKN : ((K * Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (absNorm_mem_idS I)
    refine ⟨fun t ht => ?_, K * (Ideal.absNorm I * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu hh t => ?_,
      fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg fun h' => h h'.1)
    · have hH : IsHalf e (t + (K * (Ideal.absNorm I * M)) • u) ↔ IsHalf e t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have e1 : (t + (K * (Ideal.absNorm I * M)) • u) i j = t i j + ((K * (Ideal.absNorm I * M) : ℕ) : AE D) * u i j := by
          change t i j + (K * (Ideal.absNorm I * M)) • u i j = _
          rw [nsmul_eq_mul]
        rw [e1, mul_add, mul_left_comm, hh i j]
        constructor
        · intro h; exact add_right_cancel h
        · intro h; rw [h]
      have hadd : ∀ i j, frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j =
          frMapO S.V T.V S.β T.β t i j +
            ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) := by
        intro i j
        rw [GlobalTheory.PlaceDatum.frMapO_add, show K * (Ideal.absNorm I * M) = K * Ideal.absNorm I * M from (mul_assoc _ _ _).symm,
          Nat.cast_mul (K * Ideal.absNorm I) M, mul_assoc]
      have hC' : InCosetOf S T I c (t + (K * (Ideal.absNorm I * M)) • u) ↔ InCosetOf S T I c t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have hz : (M : EAf D) * frMapO S.V T.V S.β T.β u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hB u hu i j
        have hw : ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) ∈
            Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem (natCast_mem _ _) hz
        have hmem : frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
            frMapO S.V T.V S.β T.β t i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hadd]; exact add_mem_cancel_right hw
        constructor
        · rintro ⟨h1, h⟩
          exact ⟨hmem.1 h1, (mk_eq_of_eq_add _ h1 (hmem.1 h1) hz hKN (hadd i j)).symm.trans h⟩
        · rintro ⟨h2, h⟩
          exact ⟨hmem.2 h2, (mk_eq_of_eq_add _ (hmem.2 h2) h2 hz hKN (hadd i j)).trans h⟩
      unfold cosetInd
      by_cases ht : IsHalf e t ∧ InCosetOf S T I c t
      · rw [if_pos ⟨hH.2 ht.1, hC'.2 ht.2⟩, if_pos ht]
      · rw [if_neg fun h => ht ⟨hH.1 h.1, hC'.1 h.2⟩, if_neg ht]
    · have h : IsHalf e t ∧ InCosetOf S T I c t := by
        by_contra h
        exact ht (if_neg h)
      have hK' := hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf h.1) fun i j => (h.2 i j).1
      rw [mul_nsmul]
      exact nsmul_mem hK' _
  · rw [← hfun]
    exact hc

end GlobalTheory.Grid

end
