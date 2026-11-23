import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.TupleChars

variable {D : D7}

open GlobalTheory.StepLaw (ResAt UnrOff)

theorem idemSum_mul_idemAt {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) : (idem Q + cA D (idem Q)) * idemAt PP = 0 := by
  rw [idem, map_sum, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_eq_zero fun i hi => h.mul_eq_zero (hQ hi) hPP (by rintro rfl; exact hn hi),
    Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact h.mul_conj hPP (hQ hi), add_zero]

theorem idemSum_mul_of_off {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) {e : AE D} (he : IsIdemAt e PP) {x : AE D} (hx : e * (x - 1) = x - 1) :
    (idem Q + cA D (idem Q)) * x = idem Q + cA D (idem Q) := by
  have k := idemSum_mul_idemAt h hQ hPP hn
  rw [idemAt_eq he] at k
  linear_combination (-(idem Q + cA D (idem Q))) * hx + (x - 1) * k

theorem resAt_of_isResAt {χ : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {c : (kP PP)ˣ →* Circle} (h : IsResAt χ PP c) :
    ResAt χ PP (Circle.toUnits.comp c) := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  rw [h x (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm]
  rfl

theorem resAt_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet P)
    (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2 (idemSum_mul_of_off h hQ hPP hn he hx)]
  simp

theorem resAt_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (PP : Pl D.host.E) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2]
  simp

theorem resAt_twist {t : Twist D Circle} (ht : t.Good) {P : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : t.Q ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) : ResAt t.chi PP (t.locC PP) := by
  by_cases hq : PP ∈ t.Q
  · have e : t.locC PP = t.resC PP := by simp only [Twist.locC, if_pos hq]
    rw [e]
    exact resAt_of_isResAt (ht.res PP hq)
  · have e : t.locC PP = 1 := by simp only [Twist.locC, if_neg hq]
    rw [e]
    exact resAt_of_unram ht.unram h hQ hPP hq

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  simp [infPart, Algebra.TensorProduct.algebraMap_apply]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem infPart_eq_one {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x : AE D}
    (h : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  have k := congrArg (infPart D) h
  rw [map_mul, map_sub, map_one, infPart_placeIdem hε, zero_mul] at k
  linear_combination -k

theorem unrOff_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet Q)
    (hQ : Q ⊆ P) : UnrOff χ P := by
  intro v ε hε hv x h1 h2 h3
  refine hχ x (infPart_eq_one hε h1) h2 h3 ?_
  have k : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v', ε', hε', he⟩ := (h.isIdemAt hPP).1
    have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v' ε' (h.isIdemAt hPP) hε' he
    rw [he, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε fun e => hv PP (hQ hPP) (hu.trans e), map_zero]
  linear_combination (-(idem Q + cA D (idem Q))) * h1 + ((x : AE D) - 1) * k

theorem unrOff_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (P : Finset (Pl D.host.E)) :
    UnrOff χ P := fun _ _ hε _ x h1 h2 h3 => hχ x (infPart_eq_one hε h1) h2 h3

theorem tuple_chars : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q →
    (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧
      GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
    GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  intro D S T B hB ν hν hA
  classical
  obtain ⟨P, hPg, hQP, hP⟩ := hA.1.split
  have hsub : allP B ν.Q ⊆ P := Finset.union_subset hPg hQP
  have hdeP : B.de.Q ⊆ P := fun x hx => hQP (Finset.mem_union_left _ hx)
  have hνP : ν.Q ⊆ P := fun x hx => hQP (Finset.mem_union_right _ hx)
  have hη : UnramEverywhere D B.eta := hB.eta.2.1
  have key : ∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) := by
    intro PP hPP
    have hPPP := hsub hPP
    have hνr := resAt_twist hν hP hνP hPPP
    by_cases hg : PP ∈ B.G.Pg
    · have hde : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hA.1.disj hg (Finset.mem_union_left _ h)
      have hdl : B.de.locC PP = 1 := by simp only [Twist.locC, if_neg hde]
      rw [resP, if_pos hg, hdl, mul_one]
      exact ResAt.mul (resAt_of_isResAt (hB.tame PP hg)) hνr
    · rw [resP, if_neg hg]
      exact ResAt.mul (ResAt.mul (resAt_of_unram hB.unram hP hPg hPPP hg) (resAt_twist hB.de hP hdeP hPPP)) hνr
  have u1 : UnrOff (B.mu * ν.chi) (allP B ν.Q) :=
    UnrOff.mul (UnrOff.mul (unrOff_of_unram hB.unram (hP.mono hPg) (by intro x hx; simp [allP, hx]))
      (unrOff_of_unram hB.de.unram hB.de.split (by intro x hx; simp [allP, hx])))
      (unrOff_of_unram hν.unram hν.split (by intro x hx; simp [allP, hx]))
  refine ⟨fun PP hPP => ⟨key PP hPP, ?_⟩, u1, u1.mul (unrOff_of_unramEverywhere hη _).inv⟩
  have := (key PP hPP).mul (resAt_of_unramEverywhere hη PP).inv
  rwa [inv_one, mul_one] at this

end GlobalTheory.ExportSeries.TupleChars

end
