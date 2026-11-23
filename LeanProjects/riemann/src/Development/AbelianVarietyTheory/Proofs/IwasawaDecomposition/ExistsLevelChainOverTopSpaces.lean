import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBasisAdapted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHilbertChainOfLevelOverTopsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopSpacesMapOntoChainTopInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypePartsSpanAndOrthogonalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.ChainLevel

set_option maxHeartbeats 4000000 in

theorem chain_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  obtain ⟨jX, hjX, htop⟩ := GlobalTheory.T.topSpaces_map_onto_chainTop_in_coordinates D G Pl0 I0 T A3 Ks R F cG hI hP hH y b m s tA hA
  obtain ⟨EE, Mult, mZ, mT, io, jE, jM, hEi, hEr, hEip, hM, hio0, hio, hioT, hjunk⟩ :=
    GlobalTheory.T.exists_hilbertChain_of_level_over_tops D (y.C F.lv2) b y.Us (fun μ => (s μ).A) jX D.R.two_le_m (h1 b).1 (h1 b).2 (h2 b) hjX
  obtain ⟨hsup, horth⟩ := GlobalTheory.T.rowFiniteTypeParts_span_and_orthogonal D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hR b
  classical
  haveI : Finite Φ := hR.fin
  haveI : Fintype Φ := Fintype.ofFinite Φ
  have hle : ∀ π, y.prtE F.lv2 b (rep π) ≤ LinearMap.range jE := fun π => hEr ▸ hsup ▸ le_iSup (fun π => y.prtE F.lv2 b (rep π)) π
  let p : Φ → Submodule ℂ EE.T := fun π => (y.prtE F.lv2 b (rep π)).comap jE
  have hmap : ∀ π, (p π).map jE = y.prtE F.lv2 b (rep π) := fun π => Submodule.map_comap_eq_of_le (hle π)
  have hptop : (⨆ π, p π) = ⊤ := by
    apply Submodule.map_injective_of_injective hEi
    rw [Submodule.map_iSup, Submodule.map_top, hEr]
    simp only [hmap]
    exact hsup
  have hporth : ∀ π π', π ≠ π' → p π ⟂ p π' := by
    intro π π' hne
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [hEip]
    exact horth π π' hne _ hu _ hv
  obtain ⟨bs, ty, hft⟩ := GlobalTheory.Mem.exists_orthonormalBasis_adapted EE.T Φ p hptop hporth
  have hdisj : ∀ π π', π ≠ π' → y.prtE F.lv2 b (rep π) ⊓ y.prtE F.lv2 b (rep π') = ⊥ := by
    intro π π' hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hxE : x ∈ (y.C F.lv2).EEc b := hEr ▸ hle π hx1
    have h0 := horth π π' hne x hx1 x hx2
    by_contra hne0
    have := (h1 b).1.pos ⟨x, hxE⟩ (fun h => hne0 (by simpa using congrArg Subtype.val h))
    rw [h0] at this
    simp at this
  exact ⟨⟨EE, Mult, mZ, mT, io, _, bs, ty⟩, ⟨jE, jM, jX, hEi, hEr, hEip, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).1,
    fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.1, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.2,
    fun μ hμ => (hjX μ hμ).1, fun μ hμ => (hjX μ hμ).2.1, fun μ hμ => (hjX μ hμ).2.2, hio0, hio, hioT, hjunk,
    hft, hdisj, htop⟩⟩

end GlobalTheory.Mem.R3.Rw.ChainLevel
