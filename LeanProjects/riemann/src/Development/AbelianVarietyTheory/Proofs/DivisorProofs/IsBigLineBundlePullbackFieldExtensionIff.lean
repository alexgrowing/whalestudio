import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
