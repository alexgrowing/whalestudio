import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutativeStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem avg_comp_mul_left {H : Type} [Group H] (u : H → ℂ) (h : H) : avg (fun y => u (h * y)) = avg u := by
  have hR : rStab (fun y => u (h * y)) = rStab u := by
    ext k
    show (∀ x, u (h * (x * k)) = u (h * x)) ↔ ∀ x, u (x * k) = u x
    constructor
    · intro H x
      have := H (h⁻¹ * x)
      simpa [mul_assoc] using this
    · intro H x
      simpa [mul_assoc] using H (h * x)
  unfold avg
  rw [hR]
  congr 1
  calc ∑ᶠ q : H ⧸ rStab u, u (h * q.out) = ∑ᶠ q : H ⧸ rStab u, u ((h • q).out) := by
        refine finsum_congr fun q => ?_
        obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (h * q.out)
        have hq : h • q = ((h * q.out : H) : H ⧸ rStab u) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        rw [hq, hr]
        exact (r.2 (h * q.out)).symm
    _ = ∑ᶠ q : H ⧸ rStab u, u q.out := finsum_comp_equiv (MulAction.toPerm h) (f := fun q : H ⧸ rStab u => u q.out)

end PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

theorem DcCount_pf : DcCount := by
  intro G _ _ _ θ K Γ δ f _ _ hG hΓ _ _ _ _ _
  have hCT : cptPart (twCent θ δ) ≤ twCent θ δ := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hinv : ∀ t ∈ twCent θ δ, ∀ k ∈ K, ∀ x : G,
      (avg fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        avg fun k' : K => f ((x * k')⁻¹ * δ * θ (x * k')) := by
    intro t ht k hk x
    have ht' : t * δ = δ * θ t := ht
    have e1 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : ∀ y : G, (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
      intro y
      rw [map_mul, _root_.mul_inv_rev]
      calc y⁻¹ * t⁻¹ * δ * (θ t * θ y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by simp only [mul_assoc]
        _ = y⁻¹ * δ * θ y := by rw [e1]
    have e3 : (fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        fun k' : K => (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) (⟨k, hk⟩ * k') := by
      funext k'
      have : t * x * k * (k' : G) = t * (x * ((⟨k, hk⟩ * k' : K) : G)) := by simp [mul_assoc]
      rw [this, e2]
    rw [e3]
    exact DoubleCosetCounting.avg_comp_mul_left (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) ⟨k, hk⟩
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative G (twCent θ δ) Γ (cptPart (twCent θ δ)) K
    (fun x => avg fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))) hG.1 hCT hG.2 hinv
  rw [inf_eq_left.2 hΓ] at hreg
  have key : dcSum Γ K (fun x => f (x⁻¹ * δ * θ x)) =
      ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
        ((Nat.card (Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ *
          avg (fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))) := by
    unfold dcSum
    exact finsum_congr fun q => by rw [div_eq_inv_mul]
  rw [key, hreg]
  rfl

end PositivityTheory.Rg.BcB.G8.Fin

end
