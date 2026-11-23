import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow

theorem isOpen_closure_of_isOpen_components {Z : Type} [TopologicalSpace Z]
    (h : ∀ z : Z, IsOpen (irreducibleComponent z)) {W : Set Z} (hW : IsOpen W) : IsOpen (closure W) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨irreducibleComponent z, ?_, h z, mem_irreducibleComponent⟩
  have hne : (irreducibleComponent z ∩ W).Nonempty := mem_closure_iff.1 hz _ (h z) mem_irreducibleComponent
  intro y hy
  refine mem_closure_iff.2 fun O hO hyO => ?_
  obtain ⟨a, -, ha⟩ := isIrreducible_irreducibleComponent.isPreirreducible O W hO hW ⟨y, hy, hyO⟩ hne
  exact ⟨a, ha⟩

theorem isOpen_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens), IsClosed (U : Set (Xo.XF c)) → IsOpen (FramedFlatCoordinates.compactification Y U) := by
  intro E _ _ _ H Dw l Xo c Y U _
  have i₀ : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have i₁ : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hn : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := fun x => by
    let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (FramedFlatCoordinates.genFibre Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (RingHom.id c.F)))
  have := Y.jQ_open
  exact isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)

end GlobalTheory.FlatRow
