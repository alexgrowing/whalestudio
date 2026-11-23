import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Development.EtaleCohomology.EtaleTrace.LFinCut

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.compSum_of :
    CompSum := by
  intro k _ X p hs hpr
  haveI := hs
  haveI := hpr
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : GlobalTheory.IsNormalScheme X := LateralTheory.EtaleTrace.LFinCut.normal_of_smooth p
  haveI : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := {}
  haveI : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  have hopen : ∀ Z : irreducibleComponents X, IsOpen (Z : Set X) :=
    fun Z => (GlobalTheory.IsNormalScheme.component Z).isOpen
  refine ⟨Nat.card (irreducibleComponents X), fun s => (GlobalTheory.IsNormalScheme.component (e.symm s) : Scheme),
    fun s => (GlobalTheory.IsNormalScheme.component (e.symm s)).ι, ⟨fun s => inferInstance, ?_, ?_⟩, ?_⟩
  · intro x
    refine ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι, Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  · intro s s' hss'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have hne : e.symm s ≠ e.symm s' := fun h => hss' (e.symm.injective h)
    show Disjoint ((e.symm s : Set X)) ((e.symm s' : Set X))
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hne
    have h12 : ((e.symm s : Set X)) ⊆ (e.symm s' : Set X) :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen (e.symm s).2.1.isPreirreducible
        (hopen (e.symm s')) hn).trans
        (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents _ (e.symm s').2))
    exact Subtype.ext (le_antisymm h12 ((e.symm s).2.2 (e.symm s').2.1 h12))
  · intro s
    haveI : IsReduced X := by
      haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
        obtain ⟨hd, -⟩ := ‹GlobalTheory.IsNormalScheme X›
        haveI := hd x
        infer_instance
      exact isReduced_of_isReduced_stalk X
    haveI : IrreducibleSpace ((GlobalTheory.IsNormalScheme.component (e.symm s) : X.Opens) : Set X) :=
      Subtype.irreducibleSpace (e.symm s).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
