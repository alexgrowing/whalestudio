import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsEmbeddingOfRingTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.RecursiveTieLevelZeroEq
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.HermitianColumns.FullSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack

namespace GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable (D : D7) (L0 : LevelData D)

def Companion : Prop :=
  ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
    (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0

def stdBasis (hS : Formalism.L2.Herm.StdTied D) : GL (Fin D.R.k) D.host.E := Classical.choose (exists_stdB_of_tied D hS)

theorem stdBasis_std (hS : Formalism.L2.Herm.StdTied D) : Cmp.StdB D (stdBasis D hS) := Classical.choose_spec (exists_stdB_of_tied D hS)

def placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  locIdStd D u w hg (Classical.choose (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)) (stdBasis D hS) (stdBasis_std D hS)
    (Classical.choose (hC u)) (Classical.choose_spec (hC u))

def embK (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg))

def embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))

theorem embK_embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (z : D.what₂.LL) : embK D L0 u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) = lamV (embAlg D L0 u w hg) (D.what₂.embLL z) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).1 z

def awayChar (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ :=
  Classical.choose (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg)

def gatOf (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (sc : Scale) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GAtP (D.what₂.places.resChar w) :=
  (packC D (fun u => L0 u) I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc 1 (D.what₂.places.resChar w))

set_option maxHeartbeats 4000000 in
theorem gatOf_d (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (I) (ψ) (sc : Scale) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (gatOf D L0 I ψ sc u w h).d = Module.finrank ℂ (D.mem u).A.Mu0 :=
by
  have e := GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h (I u w h) (ψ u w h) (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))
  rw [pack_eq] at e
  exact e

section Main

variable {D L0}

set_option maxHeartbeats 4000000 in
theorem posOK_placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0)
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (packC D (fun u => L0 u) (placeId D L0 hS hC) ψ u w hg).posOK (embK D L0 u w hg) (embAlg D L0 u w hg) := by
  have e := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).2 (ψ u w hg)
  unfold LocPack.posOK at e ⊢
  exact e

end Main

section Main2

variable {D L0}

end Main2

theorem gPlTiedS_of {X : D7} {Gt : GatTies X} (H0 : Formalism.L2.Herm.Herm0 X)
    (hpl : ∀ u w hg (v : Fin (X.gat u w hg).P.nV) (s : Fin ((X.gat u w hg).P.n' v)) (x : 𝓞 X.host.F),
      x ∈ ((H0.g u w hg).pl v).1.asIdeal ↔
        (0 : WithTop ℤ) < X.what₂.places.val w (tauLL X (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap X.host.F X.host.E (x : X.host.F))))
    (B : Formalism.L2.Herm.HermColsCh X) (gS : Formalism.L2.Herm.SymmetricGroupCompatibility X B) (hB : B.lev0 = H0.lev0) (hg : HEq gS H0.g) :
    Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces X B gS Gt := by
  obtain ⟨l, g⟩ := H0
  dsimp only at hB hg hpl
  subst hB
  obtain rfl := eq_of_heq hg
  exact hpl

end GlobalTheory.Mem.ConcreteRecord
