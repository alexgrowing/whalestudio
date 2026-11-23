import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.EisBL.DoubledGroupTopology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isClosed_UG {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [T2Space B] (c : B →ₐ[A] B) (hc : Continuous c) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι B) :
    IsClosed (UG c J : Set (GL ι B)) := by
  have hf : Continuous fun g : GL ι B => (g : Matrix ι ι B)ᵀ * J * (g : Matrix ι ι B).map c :=
    ((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)
  exact isClosed_singleton.preimage hf

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA (F := F) (E := E) σ) :=
  IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem isClosed_doubled_group (σ : E →ₐ[F] E) {n : ℕ} (Y : Spc F E n) :
    IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) :=
  isClosed_UG (cA σ) (continuous_cA σ) _

instance t2GL {ι : Type} [Fintype ι] [DecidableEq ι] : T2Space (GL ι (AE F E)) :=
  Units.isEmbedding_embedProduct.t2Space

instance secondCountableGL {ι : Type} [Fintype ι] [DecidableEq ι] : SecondCountableTopology (GL ι (AE F E)) := by
  have : SecondCountableTopology (Matrix ι ι (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → AE F E))
  have : SecondCountableTopology (Matrix ι ι (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

instance locCompactGL {ι : Type} [Fintype ι] [DecidableEq ι] : LocallyCompactSpace (GL ι (AE F E)) := by
  have : LocallyCompactSpace (Matrix ι ι (AE F E)) := inferInstanceAs (LocallyCompactSpace (ι → ι → AE F E))
  have : LocallyCompactSpace (Matrix ι ι (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

instance t2G2 : T2Space (G2 σ Y) := inferInstance

instance secondCountable_adelic_GL2 : SecondCountableTopology (G2 σ Y) :=
  (isClosed_doubled_group σ Y).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

instance locallyCompactDoubledGroup : LocallyCompactSpace (G2 σ Y) :=
  (isClosed_doubled_group σ Y).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem countable_rational_points_doubled (σ : E →ₐ[F] E) {n : ℕ} (Y : Spc F E n) : Countable (rat2 σ Y) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := E)
  haveI : Countable (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :=
    inferInstanceAs (Countable (Fin n ⊕ Fin n → Fin n ⊕ Fin n → E))
  haveI : Countable (GL (Fin n ⊕ Fin n) E) := Function.Injective.countable (fun a b h => Units.ext h)
  have hr : (Set.range (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)))).Countable :=
    Set.countable_range _
  haveI := hr.to_subtype
  refine Function.Injective.countable (f := fun x : rat2 σ Y =>
    (⟨(x.1 : GL (Fin n ⊕ Fin n) (AE F E)), x.2⟩ : Set.range (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))))) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))

end GlobalTheory.EisBL.DoubledGroupTopology
