import Mathlib
import GroundTheory.GlobalFields.Artin.InductionLocal
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField GroundTheory.LocalField

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem under_eq_iff_liesOver (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 (fixedField H))) :
    u.under (𝓞 K) = v ↔ u.asIdeal.LiesOver v.asIdeal := by
  rw [HeightOneSpectrum.ext_iff, Ideal.liesOver_iff, HeightOneSpectrum.under_asIdeal, eq_comm]

open Classical in

theorem tsum_under_eq_sum (v : HeightOneSpectrum (𝓞 K))
    (g : HeightOneSpectrum (𝓞 (fixedField H)) → ℂ) :
    ∑' c : {u : HeightOneSpectrum (𝓞 (fixedField H)) // u.under (𝓞 K) = v}, g c =
      ∑ q : DoubleCoset.Quotient (H : Set Gal(L/K))
          (MulAction.stabilizer Gal(L/K) (placeAbove (L := L) v).asIdeal),
        g (subfieldPlace H (placeAbove (L := L) v) q.out) := by
  set w := placeAbove (L := L) v
  let E := (subfieldPlaceEquiv H v w).trans
    (Equiv.subtypeEquivRight (under_eq_iff_liesOver H v)).symm
  rw [← E.tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  change ((subfieldPlaceEquiv H v w q : HeightOneSpectrum (𝓞 (fixedField H)))) = _
  have h := subfieldPlaceEquiv_mk H v w q.out
  rw [DoubleCoset.out_eq'] at h
  exact h

open Classical in

theorem artinLogL_indFun [Fintype Gal(L/K)] [Fintype H] {f : H → ℂ} (hf : IsClassFun f) {s : ℂ}
    (hs : 1 < s.re) :
    artinLogL K L (indFun H.subtype f) s = artinLogL (fixedField H) L (fixedFieldFun H f) s := by
  have hg : Summable (artinLocalLog (fixedField H) L (fixedFieldFun H f) s) :=
    (hasSum_artinLocalLog_artinLogL (fixedFieldFun H f) hs).summable
  let e := Equiv.sigmaFiberEquiv fun u : HeightOneSpectrum (𝓞 (fixedField H)) ↦ u.under (𝓞 K)
  have hge : Summable fun p ↦ artinLocalLog (fixedField H) L (fixedFieldFun H f) s (e p) :=
    (e.summable_iff).2 hg
  rw [artinLogL, artinLogL, ← e.tsum_eq, hge.tsum_sigma]
  refine tsum_congr fun v ↦ ?_
  rw [artinLocalLog_indFun H hf hs v]
  exact (tsum_under_eq_sum H v (artinLocalLog (fixedField H) L (fixedFieldFun H f) s)).symm

theorem artinL_indFun [Fintype Gal(L/K)] [Fintype H] {f : H → ℂ} (hf : IsClassFun f) {s : ℂ}
    (hs : 1 < s.re) :
    artinL K L (indFun H.subtype f) s = artinL (fixedField H) L (fixedFieldFun H f) s := by
  rw [artinL, artinL, artinLogL_indFun H hf hs]

end GroundTheory.Global.Artin
