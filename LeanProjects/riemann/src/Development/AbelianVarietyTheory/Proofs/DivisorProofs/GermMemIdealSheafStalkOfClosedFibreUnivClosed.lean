import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.SpreadIdeal

theorem exists_open_nhds_mem_stalkId (P : Scheme.{0}) (I : P.IdealSheafData) (s : Γ(P, ⊤)) (v : P)
    (hv : (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) :
    ∃ O : P.Opens, v ∈ O ∧ ∀ y ∈ O, (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(P, U) (P.presheaf.stalk v) := P.presheaf.algebra_section_stalk ⟨v, hvU⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hvU⟩
  set t : Γ(P, U) := P.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : P) (hy : y ∈ U), (P.presheaf.germ ⊤ y trivial).hom s =
      (P.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, P.presheaf.germ_res]
  rw [hgerm v hvU, ds_stalkId_eq_map I ⟨U, hU⟩ v hvU] at hv
  change algebraMap Γ(P, U) (P.presheaf.stalk v) t ∈
    Ideal.map (algebraMap Γ(P, U) (P.presheaf.stalk v)) (I.ideal ⟨U, hU⟩) at hv
  obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl _).mp hv
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) e
  set σ : Γ(P, U) := (c : Γ(P, U)) * w with hσ
  have hσt : σ * t ∈ I.ideal ⟨U, hU⟩ := by
    rw [hσ, show (c : Γ(P, U)) * w * t = c * (t * w) by ring, hc]
    exact Ideal.mul_mem_left _ _ a.2
  have hσunit : IsUnit (algebraMap Γ(P, U) (P.presheaf.stalk v) σ) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) _
      (c * w : (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl)
  refine ⟨P.basicOpen σ, ?_, fun y hy => ?_⟩
  · exact (P.mem_basicOpen σ v hvU).mpr hσunit
  · have hyU : y ∈ U := P.basicOpen_le σ hy
    have hyu : IsUnit ((P.presheaf.germ U y hyU).hom σ) := (P.mem_basicOpen σ y hyU).mp hy
    rw [hgerm y hyU, ← Ideal.unit_mul_mem_iff_mem _ hyu, ← map_mul,
      ds_stalkId_eq_map I ⟨U, hU⟩ y hyU]
    exact Ideal.mem_map_of_mem _ hσt

end GlobalTheory.SpreadIdeal

namespace GlobalTheory.SpreadIdeal

theorem mem_stalkId_of_closedFibre : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro P R _ _ p _ I s hs v
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  have himg : IsClosed (p.base '' Z) := p.isClosedMap _ hZc
  have hmem : closedPoint R ∈ p.base '' Z :=
    (IsLocalRing.specializes_closedPoint (p.base v)).mem_closed himg ⟨v, hv, rfl⟩
  obtain ⟨w, hwZ, hw⟩ := hmem
  exact hwZ (hs w hw)

end GlobalTheory.SpreadIdeal
