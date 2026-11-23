import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumMult.exists_pt_chart_of_leadPt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i')), GlobalTheory.MumMult.LeadPt U b m → ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ GlobalTheory.MumMult.multW U b 0 i i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  intro R _ _ _ D A G _ _ U b m hL
  obtain ⟨x, hx, H⟩ := hL

  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1))))
  have hp : (thick R (maximalIdeal R) 0) p = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) p.asIdeal = maximalIdeal R
    refine ((maximalIdeal.isMaximal R).eq_of_le (p.isPrime.comap _).ne_top ?_).symm
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hr)]
    exact p.asIdeal.zero_mem
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom)
    (g := thick R (maximalIdeal R) 0) x p (hx.trans hp.symm)
  obtain ⟨y, hy⟩ := (U.gt 0).q_surj.surj z
  refine ⟨y, ?_, ?_⟩
  · have hc := U.LG.isLB.cover
    have hmem : (fstG (maximalIdeal R) 0 G).left y ∈ (⨆ j, U.LG.L.U j) := by rw [hc]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact ⟨fun _ => j, Set.mem_iInter.2 fun _ => hj⟩
  · intro i i' hy'
    refine H y ?_ i i' hy'
    show (D.toPre.prBe (maximalIdeal R) 0).left ((U.gt 0).q.left y) = x
    rw [hy]
    exact hz
