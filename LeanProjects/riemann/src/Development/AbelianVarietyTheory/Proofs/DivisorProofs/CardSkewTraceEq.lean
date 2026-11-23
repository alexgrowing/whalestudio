import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewTangentReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraFiniteCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormResidueFieldDataStatement

open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong

theorem exists_resInv {A : Type} [CommRing A] (S : Subring A) (σ : A →+* A) (ϖ : A) (hϖ : ϖ ∈ S)
    (hσ : ∀ s ∈ S, σ s ∈ S) (hσϖ : σ ϖ = ϖ) :
    ∃ τ : Res S ϖ →+* Res S ϖ, ∀ a ∈ S, τ (red S ϖ a) = red S ϖ (σ a) := by
  let σS : S →+* S :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hle : piIdeal S ϖ ≤ Ideal.comap σS (piIdeal S ϖ) := by
    unfold piIdeal
    rw [Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    show σ (x : A) = ϖ
    rw [show (x : A) = ϖ from hx, hσϖ]
  refine ⟨Ideal.quotientMap (piIdeal S ϖ) σS hle, fun a ha => ?_⟩
  unfold red
  rw [dif_pos ha, dif_pos (hσ a ha), Ideal.quotientMap_mk]
  rfl

theorem card_skewTr : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → Nat.card (skewTr S σ H ϖ) = q ^ (Fintype.card n ^ 2 - 1) := by
  intro A _ n _ _ S σ H ϖ q hR hF
  obtain ⟨τ, hτ⟩ := exists_resInv S σ ϖ hR.2.2.1 hR.2.1 hR.2.2.2.1
  obtain ⟨k, w, H', hk, hw1, hwu, hdec, hinv, hq, hH, hH'⟩ := GlobalTheory.T.good_form_residue_field_data S σ H ϖ q τ hR hF hτ
  rw [GlobalTheory.T.skew_tangent_reduction S σ H ϖ τ hR.2.2.1 hR.2.1 hF.1 hτ]
  exact GlobalTheory.T.unitary_lie_algebra_finite_card τ k w _ H' q hk hw1 hwu hdec hinv hq hH hH'

end GlobalTheory.SUCong
