import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Sd.S2.emb (k F Ω : Type) [Field k] [NumberField k] [Field F] [NumberField F] [Field Ω] [Algebra k F] [Algebra k Ω]
    [Algebra F Ω] [IsScalarTower k F Ω] [IsAlgClosure k Ω] : Topology.IsEmbedding (galEmb k F Ω) :=
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed k, Algebra.IsAlgebraic.tower_top (K := k) F⟩
  (galEmbTop k F Ω).1
