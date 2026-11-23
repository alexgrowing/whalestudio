import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.lat_gmap {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {F0' : LFlag (VS D) D.R.rS T'} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem GFrames.datOf_N_fst (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N) (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).1 = (G.datOf Γ p).1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N, A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.1 g' hgN (A.lat p Γ)

theorem GFrames.datOf_N'_snd (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N') (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).2.1 = (G.datOf Γ p).2.1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N', A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.2.1 g' hgN (A.lat p Γ)
end Loc

theorem datOf_dcoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv t n m hlam hlam' hnm p
  obtain ⟨hn, hm, hlin⟩ := hnm
  obtain ⟨P1, P2, P3, -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv

  have hrel : ∀ s : TauC Y u u', Formalism.HermitianLatticesTheory.gmap (GTerm.lin s) s.lam' = s.lam :=
    fun s => (Quot.out s.cls).property.2.2.1
  constructor
  · rw [P3, hlam]
    exact GFrames.datOf_N_fst G ((P1 n).1 hn) _ p
  · have e1 : c.lat (ρ * n) t.lam = (c.lat (ρ * GTerm.lin t₀) t₀.lam').map
        (((c.grp (ρ * GTerm.lin t₀) m : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
      rw [← P3, ← hrel t, GCoord.lat_gmap, hlin, hlam']
      congr 1
      group
    have e2 : c.lat (ρ * GTerm.lin t₀) t₀.lam' = c.lat ρ t₀.lam := by
      rw [← GCoord.lat_gmap, hrel t₀]
    rw [e1, ← e2]
    exact GFrames.datOf_N'_snd G ((P2 m).1 hm) _ p

end GlobalTheory.HL
