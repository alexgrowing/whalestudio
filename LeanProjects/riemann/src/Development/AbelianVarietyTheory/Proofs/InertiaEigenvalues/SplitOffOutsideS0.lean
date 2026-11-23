import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitOffS0

theorem main : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  intro D N X ρ hρ i Q hQ P hsplit hP
  have hinv : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := fun z => Formalism.L2.Host.conj_conj (D := D) D.host z
  let c : 𝓞 D.host.E → 𝓞 D.host.E := fun x => RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := fun x => rfl
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      (x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ↔ y ∈ P.asIdeal) :=
    fun x y h => GlobalTheory.Mem.Col2.HAt.mem_conjIdeal_Pv P.asIdeal x y h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hy⟩ := hsplit
    intro heq
    have h1 : c x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal :=
      (key (c x) x (by rw [hc, hinv])).2 hx
    exact hy (c x) (hc x) (heq ▸ h1)
  · intro hPQ
    exact hP (hQ P (by simpa using hPQ))
  · intro Q' hQ' heq
    apply hP
    refine hρ.goodSetup_badPlaces_conj i Q' (hQ Q' (by simpa using hQ')) P ?_
    intro x y hxy
    rw [heq]
    exact key x y hxy

end GlobalTheory.SplitOffS0
