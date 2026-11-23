import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigTie
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct
variable {D : D7}
section Sys
variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}
end Sys
section Read
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Read
section Par
variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)
variable {C Rw Y} {i : X.Tw} {b : Bool}
end Par
section Res
variable (Rw : RowSide D)
def ReductionConditionAtPlace {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r → IsResidual ι r σ w red
end Res
def ResTiedAlt (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ι w red
section Bridge
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
theorem ResTiedAlt.exists_reading {Rw : RowSide D} (h : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw) (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hi : X.NonzeroIndexPlace i) (b : Bool) :
    ∃ (ρ : Reading X i b) (w : D.what₂.places.Pl) (red : Zbar (X.l i) →+* FbAt D w), ρ.Induces w ∧ _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ρ.ι w red := by
  obtain ⟨w, hw, H⟩ := hi
  obtain ⟨ρ⟩ := Reading.nonempty (X := X) i true
  have hl : 0 < D.what₂.places.val w ((X.l i : ℕ) : D.what₂.LL) := by
    have := (H ((X.l i : ℕ) : 𝓞 ↥D.LL0)).1 ((norm_lt_iff ρ _).2 (by
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, map_natCast,
        ← map_natCast (algebraMap ℚ_[X.l i] (Qbar (X.l i))), norm_algebraMap']
      exact Padic.norm_p_lt_one))
    simpa using this
  obtain ⟨ι, red, hι⟩ := h w hw (X.l i) (resChar_eq (X.lPrime i).out hl)
  have key : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (X.emb0 i x)‖ ≤ 1 := fun x =>
    (hι.1 x).trans (ball_of_int (ι.symm.toRingHom.comp (embLL0 D)) (ρ.κ.comp (X.emb0 i))
      (fun y => ((hι.1.lt_iff _).symm.trans (H y).symm).trans (norm_lt_iff ρ _)) x)
  cases b
  · obtain ⟨ι', red', hι'⟩ := h (D.what₂.places.conj w) (by rwa [D.what₂.muAt_conj]) (X.l i)
      (resChar_eq (X.lPrime i).out (by rwa [D.conj_val, star_natCast]))
    obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := false) ρ hι'.1 fun x => by
      rw [D.conj_val]
      exact (key ⟨_, hs x⟩).trans (by rw [← X.restX_coefficientEmbedding_conj i x ⟨_, hs x⟩ rfl]; rfl)
    exact ⟨ρ', _, red', hι'.1, hι'⟩
  · obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := true) ρ hι.1 key
    exact ⟨ρ', _, red, hι.1, hι⟩
end Bridge
namespace Model
end Model
end GlobalTheory.EigTie
end
end
