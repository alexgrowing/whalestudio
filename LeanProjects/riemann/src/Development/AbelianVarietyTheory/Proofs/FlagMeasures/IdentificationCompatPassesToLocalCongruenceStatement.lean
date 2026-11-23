import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruence
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identificationCompat_passes_to_local_congruence : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  first | exact @GlobalTheory.IotaLoc.iota_typed | exact GlobalTheory.IotaLoc.iota_typed | (intros; apply GlobalTheory.IotaLoc.iota_typed <;> assumption)
