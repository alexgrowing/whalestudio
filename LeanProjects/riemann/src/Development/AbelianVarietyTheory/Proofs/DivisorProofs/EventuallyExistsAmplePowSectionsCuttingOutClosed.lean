import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutOutSections

theorem sec_eq_zero_of_nonzeroLocus_eq_bot {Y : Scheme.{0}} [IsReduced Y] {M : LB Y} (s : M.Sec)
    (h : nonzeroLocus s = ⊥) : s = 0 := by
  apply DVR.SecOps.sec_ext
  intro k
  have hk : Y.basicOpen (s.f k) = ⊥ := le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hk
  rw [hk]
  rfl

theorem eventually_isGenerated_lbPow {X : Scheme.{0}} {N : LB X} (hN : IsAmpleLB N) :
    ∀ᶠ k in atTop, IsGenerated (lbPow N k) := by
  refine (hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_
  obtain ⟨c, u, hu⟩ := hk
  have hP := isLB_lbPow hN.isLB k
  have hT := isLB_tens (LB.isLB_triv X) hP
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP
    (by rw [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu
  exact ⟨c, v, hv⟩

theorem eventually_exists_secs_cutting_out : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  intro X _ _ p hp N Z hN
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  let U : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := fun y => hN.exists_affine_le y.2
  choose n hn s hys hle _ using hloc
  have hc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X))
    (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_isGenerated_lbPow hN)
  refine eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩
  obtain ⟨c, g, hg⟩ := hK (l - m) (by omega)
  have hml : m + (l - m) = l := by omega
  let κ' : T × Fin c → (lbPow N l).Sec := fun q => secCast hml (secMul (t q.1) (g q.2))
  have hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2) := fun q => by
    simp only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]
  have hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q) := fun q y hy h => by
    rw [hκ'] at h
    exact hle _ h.1 hy
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (T × Fin c)
  refine ⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩
  · have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
    apply sec_eq_zero_of_nonzeroLocus_eq_bot
    rw [GlobalTheory.nonzeroLocus_secPull]
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : redι Z z ∈ (Z : Set X) := by
      rw [← range_redι Z]
      exact Set.mem_range_self z
    exact hb _ _ hz' hz
  · obtain ⟨a, ha', hya'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))
    refine ⟨e (⟨a, ha'⟩, j), ?_⟩
    show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))
    rw [e.symm_apply_apply, hκ']
    exact ⟨hya', hj⟩

end GlobalTheory.CutOutSections
