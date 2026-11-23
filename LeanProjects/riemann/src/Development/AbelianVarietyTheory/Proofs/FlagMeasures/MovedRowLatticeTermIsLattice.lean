import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem isLattice_map_equiv {E : Type} [Field E] [NumberField E] {V W : Type} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (e : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E))) := by
  refine ⟨hΛ.fg.map _, ?_⟩
  have h1 : ((Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E)) : Submodule (𝓞 E) W) : Set W) =
      (e : V →ₗ[E] W) '' (Λ : Set V) := by
    simp [Submodule.map_coe]
  rw [h1, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

theorem term_lat_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  intro D X Y u u' Z T T' F0 F0' FP G c t ρ
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hL : Submodule.IsLattice D.host.E t.lam := hrow.1.1
  exact isLattice_map_equiv (ρ.trans c.e) t.lam hL

end GlobalTheory.HL
