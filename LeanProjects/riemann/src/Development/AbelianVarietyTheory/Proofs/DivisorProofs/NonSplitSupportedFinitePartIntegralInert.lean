import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocalPoint

open GlobalTheory.BotClassDict GlobalTheory.NormRatio GlobalTheory.NormRatio.StdLevel

theorem idem_mul_idem {D : D7} {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε η : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hη : IsPlaceIdem D w η) (hne : w ≠ v) : η * ε = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨β, rfl, -, k0⟩ := hη
  refine Prod.ext (zero_mul (0 : Ainf D.host.F)) (FiniteAdeleRing.ext _ fun u => ?_)
  change β u * α u = 0
  by_cases hu : u = v
  · have : β u = 0 := k0 u (hu ▸ hne.symm)
    rw [this, zero_mul]
  · have : α u = 0 := h0 u hu
    rw [this, mul_zero]

theorem suppInert_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) {g : GA D V} (hg : GlobalTheory.WeilParts.SuppPl ε V g) :
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q hq hnI i j
  have e : ((finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = finQ D ((Formalism.L2.Theta.mt V g - 1) i j) := by
    rw [Matrix.sub_apply, RingHom.map_sub, finStd_apply]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  rw [e]
  refine (GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff D q hq _).2 fun w η hη hqw => ?_
  have hne : w ≠ v := by
    rintro rfl
    exact hnI ((GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq w ε hv.1 hqw).2 hv)
  rw [← hg i j, ← mul_assoc, ← map_mul, idem_mul_idem hv.1 hη hne, map_zero, zero_mul]

theorem intG_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V}
    (h : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) ↔
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E
        ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) :
    Formalism.MainNotions.StandardLatticesGL3.IntG D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← toAfE_int_iff, toAfE_finStd, mem_intAE_iff_swap]
  have e2 : ((↑(finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
      ↑(finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
  have hR : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, y i ∈ intSub D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intSub D := fun y =>
    (mem_latHat_stdLat V y).symm.trans ((h y).trans (mem_latHat_stdLat V _))
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨ha, hb⟩ := (preserves_iff (intSub D) _ _ h1 h2).1 hR
  intro i j
  rw [e2]
  exact ⟨(e1 g i j).2 (ha i j), (e1 g⁻¹ i j).2 (hb i j)⟩

theorem suppInert_and_intG : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun V hG _ _ hv _ hg h => ⟨suppInert_finStd V hG hv hg, intG_finStd V hG h⟩

end GlobalTheory.InertLocalPoint
