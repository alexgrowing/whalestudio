import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem formallyUnramified_residue_comp_of_isEtaleCompletion :
    ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A]
      (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  intro k _ m e _ A _ _ φ hφ
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    constructor
    intro a ha
    by_contra hna
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have h2 : φ a ∈ maximalIdeal (ChartRing k m e) := hmax ▸ Ideal.mem_map_of_mem φ h1
    exact (mem_maximalIdeal _).1 h2 ha
  rw [← ResidueField.map_comp_residue]
  refine RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) ?_
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  haveI : CharZero (ResidueField (ChartRing k m e)) :=
    (RingHom.charZero_iff ((residue (ChartRing k m e)).comp (algebraMap k (ChartRing k m e))).injective).1 inferInstance
  haveI : CharZero (ResidueField A) := RingHom.charZero (ResidueField.map φ)
  letI := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField (ChartRing k m e)) := hfin'
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField (ChartRing k m e)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end GlobalTheory.GenFan
