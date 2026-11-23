import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.TripRho

open GlobalTheory.TwistedSelmerCompare GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions Formalism.L2.NR

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isRhoOfRow_of_frobEig : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  intro D Rw rowS hRho hGP a σ s hRT hs hj hg hloc hfe
  obtain ⟨hiso, hgood, hspec⟩ := hRho (D.ntw.twOf a) s
  have hjr := D.nd.j_range a
  have hσs : D.what₂.isot (D.nd.j a) (rowS _ s) ≠ ⊥ := by rw [← hj]; exact hiso
  obtain ⟨π', hc', hr', hl', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 (rowS _ s) hσs hgood
  obtain ⟨π'', -, -, hl'', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 σ hg.1 hg.2
  obtain ⟨φ, ι, h1, h2, h3⟩ := hRT
  have h2' : ∀ x : ↥D.LL0, ι (φ ((if D.ntw.side (D.ntw.twOf a) s then D.ntw.emb0 (D.ntw.twOf a)
      else D.ntw.emb0b (D.ntw.twOf a)) x)) = embLL0 D x := by
    intro x; rw [hs]; exact h2 x
  obtain ⟨-, hss, hev⟩ := hspec π' hc' hr' hl' φ ι h1 h2'
  refine ⟨?_, ?_⟩
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    have e1 : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    have e2 : mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
        (D.ntw.rhoS _ s) = mapRep φ (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      rfl
    rw [e1, isSSRep_map_iff]
    rw [e2, isSSRep_map_iff] at hss
    exact hss
  · filter_upwards [hev, D.naut.locG_unr_ae π', D.naut.locG_unr_ae π'', hfe] with w hw hu' hu'' hf hsp
    intro B g hB hg'
    have hR : Rw.locR (rowS _ s) w = Rw.locR σ w := by
      have u1 : D.naut.unr (Rw.locR (rowS _ s) w) := by rw [← hl' w hsp]; exact hu'
      have u2 : D.naut.unr (Rw.locR σ w) := by rw [← hl'' w hsp]; exact hu''
      rw [D.naut.unr_eq_lpUnr _ u1, D.naut.unr_eq_lpUnr _ u2, hf hsp]
    have hpar : D.naut.locG (D.naut.tw π' D.naut.etaTinv) w =
        D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [D.naut.locG_tw, hl' w hsp, hR, hloc w hsp]
    have hcp := hw B g hB hg'
    rw [hpar] at hcp
    refine Eq.trans ?_ hcp
    have hcomp : (iotaO D.nd D.naut a).comp (D.ntw.twist₂ a) =
        ι.toRingHom.comp (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := by
      ext y
      exact (h3 y).symm
    have e1 : ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map (D.ntw.twist₂ a) := rfl
    have e2 : ((mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
          (D.ntw.rhoS (D.ntw.twOf a) s) g : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map
            (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := rfl
    rw [e1, Matrix.charpoly_map, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, ← e2]

end GlobalTheory.TripRho

end
