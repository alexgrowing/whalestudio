import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToLinTransposeDot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfSubsingletonPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedOfIntegers

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem isConn_of_retract {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Nontrivial O] {G H : PDivGroup p O}
    (f : H ⟶ G) (r : G ⟶ H) (h : f ≫ r = 𝟙 H) (hG : GlobalTheory.PDivLat.IsConn G) : GlobalTheory.PDivLat.IsConn H := by
  intro n
  have hs : Function.Surjective (f.app n) := fun a => ⟨r.app n a, by
    have := congrArg (fun g => Hom.app g n) h
    exact DFunLike.congr_fun this a⟩
  haveI : Nontrivial (H.A n) :=
    (Bialgebra.counitAlgHom O (H.A n) : H.A n →+* O).domain_nontrivial
  haveI := hG n
  exact IsLocalRing.of_surjective' (f.app n : G.A n →+* H.A n) hs

theorem hasDatum_of_conn_dual_conn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hyp G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨G₁, G₂, hs, hc₁, hk₂⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G
  obtain ⟨H₁, H₂, hs', hcH, hkH⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G₁.dual
  obtain ⟨i₁, -, q₁, -, e₁, -⟩ := id hs'
  have hD : GlobalTheory.PDivLat.IsConn H₁.dual :=
    isConn_of_retract (dualHom _ _ q₁ ≫ G₁.bidual.inv) (G₁.bidual.hom ≫ dualHom _ _ i₁)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, ← dualHom_comp, e₁, dualHom_id]) hc₁
  have dD := GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε _ _ _ hs' (hyp H₁ hcH hD)
    (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε H₂ hkH)
  have d₁ := GlobalTheory.PDivLat.hasDatum_of_iso p C v O hv ε hε _ _ ⟨G₁.bidual.symm⟩
    (GlobalTheory.DualDatum.hasDatum_dual p C v O hv ε hε _ dD)
  exact GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε G G₁ G₂ hs d₁ (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε G₂ hk₂)

end GlobalTheory.PDivLat
