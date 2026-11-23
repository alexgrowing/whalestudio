import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.LocGL
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.subPerm :
    UpperTheory.Gal.Join.SubPerm := by
  intro k _ _ _ _ n V _ _ π hi ω hω w h
  have hw : ∀ i, IsSmoothChar ((ω ∘ w) i) := fun i => hω (w i)
  have h1 := (UpperTheory.Gal.LocD.ofSupport k n V π ω hω).2 ⟨hi, h⟩
  have e : (Finset.univ.val.map fun i => IrrGL.ofChar ((ω ∘ w) i) (hw i)) =
      Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i) := by
    have e' := congrArg (Multiset.map fun i => IrrGL.ofChar (ω i) (hω i)) (Multiset.map_univ_val_equiv w)
    rw [Multiset.map_map] at e'
    exact e'
  rw [← e] at h1
  exact ((UpperTheory.Gal.LocD.ofSupport k n V π (ω ∘ w) hw).1 h1).2
