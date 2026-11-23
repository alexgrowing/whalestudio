import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uIdealSt_holds : UIdealSt := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C
  haveI : IsNoetherianRing C.o := C.ded.toIsDedekindRing.toIsNoetherian
  haveI : AlgebraicGeometry.IsNoetherian C.Z := GlobalTheory.isNoetherian_of_isProjOver C.proj
  have hdom : ∀ x : C.Z, IsDomain (C.Z.presheaf.stalk x) := fun x => C.normal.isDomain_stalk x
  have hfin : (irreducibleComponents C.Z).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  letI : Fintype (irreducibleComponents C.Z) := hfin.fintype
  have hclo : ∀ k : irreducibleComponents C.Z, IsClopen (k : Set C.Z) := fun k =>
    ⟨isClosed_of_mem_irreducibleComponents _ k.2, GlobalTheory.CompPart.isOpen_of_mem hdom k.2⟩
  have key : ∀ k : irreducibleComponents C.Z, ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, x ∈ (k : Set C.Z) ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) k φ J d := by
    intro k
    by_cases hk : ((k : Set C.Z) ∩ Set.range C.i).Nonempty
    · obtain ⟨X₁, ι, J₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk
      exact GlobalTheory.T.ideal_descent_to_component_compactification E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk X₁ ι J₁ h1 h2 h3 h4
    · refine ⟨1, ⊤, le_rfl, fun x hx => ?_, uValThru_top_of_disjoint (hclo k).2 (Set.not_nonempty_iff_eq_empty.1 hk) φ 1⟩
      rw [Scheme.IdealSheafData.support_top] at hx
      exact absurd hx (by simp [← SetLike.mem_coe])
  choose d J hd hJ hv using key
  exact exists_uValOn_of_pieces (ι := irreducibleComponents C.Z) C.i φ (fun k => (k : Set C.Z)) J d (GlobalTheory.CompPart.existsUnique_mem hdom) hd hJ hv

end GlobalTheory.UPoinc
