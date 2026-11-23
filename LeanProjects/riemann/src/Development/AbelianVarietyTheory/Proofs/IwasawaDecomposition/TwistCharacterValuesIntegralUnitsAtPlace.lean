import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem psiInt_of_embW : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  intro D C X ψ0 h j w g
  have hint : ∀ g, ∃ y : OcC X j w, algebraMap (OcC X j w) (FractionRing (OcC X j w)) y =
      ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    intro g
    have h0 : 0 ≤ D.what₂.places.val w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
      (C.embW_w w _).2 ⟨_, (h w g).symm⟩
    exact (ecC_w X j w _).1 h0
  obtain ⟨a, ha⟩ := hint g
  obtain ⟨b, hb⟩ := hint g⁻¹
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))
    rw [map_mul, ha, hb, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one, map_one]
  exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

end GlobalTheory.HeckeLocN
