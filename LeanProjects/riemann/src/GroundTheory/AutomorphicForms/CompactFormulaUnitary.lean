import Mathlib
import GroundTheory.AutomorphicForms.CompactFormulaSums
import GroundTheory.AutomorphicForms.CompactFormulaCountable
import GroundTheory.AutomorphicForms.Anisotropic

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CompactFormula

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Countable

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem secondCountableTopology_unitaryPoints (R : Type*) [CommRing R] [Algebra K R]
    [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] :
    SecondCountableTopology (unitaryPoints K E H R) := by
  have : SecondCountableTopology (R ⊗[K] E) :=
    (tensorCoordsHomeomorph R (Module.finBasis K E)).isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Matrix ι ι (R ⊗[K] E)) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → R ⊗[K] E))
  have : SecondCountableTopology (GL ι (R ⊗[K] E)) := GroundTheory.Global.secondCountableTopology_units
  have he : IsEmbedding (Subtype.val : unitaryPoints K E H R → GL ι (R ⊗[K] E)) :=
    IsEmbedding.subtypeVal
  exact he.secondCountableTopology

end Countable

variable [NumberField K]

instance secondCountableTopology_unitaryAdele :
    SecondCountableTopology (unitaryPoints K E H 𝔸[K]) :=
  secondCountableTopology_unitaryPoints H 𝔸[K]

instance t2Space_unitaryAdele [hH : Fact (IsUnit H.det)] : T2Space (unitaryPoints K E H 𝔸[K]) :=
  t2Space_unitaryPoints_adele H hH.out

instance locallyCompactSpace_unitaryAdele [hH : Fact (IsUnit H.det)] :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints_adele H hH.out

instance measurableSpace_unitaryAdele : MeasurableSpace (unitaryPoints K E H 𝔸[K]) :=
  borel _

instance borelSpace_unitaryAdele : BorelSpace (unitaryPoints K E H 𝔸[K]) :=
  ⟨rfl⟩

instance discreteTopology_unitaryRational :
    DiscreteTopology (unitaryDiagonal K H).range :=
  discreteTopology_unitaryDiagonal_range H

instance compactSpace_unitaryQuotient [hH : Fact (IsUnit H.det)]
    [haniso : Fact (∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0)] :
    CompactSpace (RightCosetSpace (unitaryDiagonal K H).range) :=
  Anisotropic.compactSpace_unitaryQuotient_of_anisotropic H hH.out haniso.out

instance isMulRightInvariant_unitaryAdele [Fact (IsUnit H.det)]
    [Fact (∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0)]
    (μ : Measure (unitaryPoints K E H 𝔸[K])) [μ.IsHaarMeasure] : μ.IsMulRightInvariant :=
  RightCosetSpace.isMulRightInvariant_of_compactSpace (unitaryDiagonal K H).range μ

variable (K) in

def unitaryAdeleGroup : Type _ := unitaryPoints K E H 𝔸[K]

instance : Group (unitaryAdeleGroup K H) := inferInstanceAs (Group (unitaryPoints K E H 𝔸[K]))

instance : TopologicalSpace (unitaryAdeleGroup K H) :=
  inferInstanceAs (TopologicalSpace (unitaryPoints K E H 𝔸[K]))

instance : IsTopologicalGroup (unitaryAdeleGroup K H) :=
  inferInstanceAs (IsTopologicalGroup (unitaryPoints K E H 𝔸[K]))

instance : SecondCountableTopology (unitaryAdeleGroup K H) :=
  inferInstanceAs (SecondCountableTopology (unitaryPoints K E H 𝔸[K]))

instance [Fact (IsUnit H.det)] : T2Space (unitaryAdeleGroup K H) :=
  inferInstanceAs (T2Space (unitaryPoints K E H 𝔸[K]))

instance [Fact (IsUnit H.det)] : LocallyCompactSpace (unitaryAdeleGroup K H) :=
  inferInstanceAs (LocallyCompactSpace (unitaryPoints K E H 𝔸[K]))

instance : MeasurableSpace (unitaryAdeleGroup K H) :=
  inferInstanceAs (MeasurableSpace (unitaryPoints K E H 𝔸[K]))

instance : BorelSpace (unitaryAdeleGroup K H) :=
  inferInstanceAs (BorelSpace (unitaryPoints K E H 𝔸[K]))

variable (K) in

def unitaryRationalGroup : Subgroup (unitaryAdeleGroup K H) := (unitaryDiagonal K H).range

instance : DiscreteTopology (unitaryRationalGroup K H) :=
  inferInstanceAs (DiscreteTopology (unitaryDiagonal K H).range)

instance [Fact (IsUnit H.det)]
    [Fact (∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0)] :
    CompactSpace (RightCosetSpace (unitaryRationalGroup K H)) :=
  inferInstanceAs (CompactSpace (RightCosetSpace (unitaryDiagonal K H).range))

instance isMulRightInvariant_unitaryAdeleGroup [Fact (IsUnit H.det)]
    [Fact (∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0)]
    (μ : Measure (unitaryAdeleGroup K H)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant :=
  RightCosetSpace.isMulRightInvariant_of_compactSpace (unitaryRationalGroup K H) μ

section TraceFormula

open RightCosetSpace

variable [Fact (IsUnit H.det)]
  [Fact (∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0)]
  (μ : Measure (unitaryAdeleGroup K H)) [μ.IsHaarMeasure]

end TraceFormula

end CompactFormula

end

end GroundTheory.Automorphic
