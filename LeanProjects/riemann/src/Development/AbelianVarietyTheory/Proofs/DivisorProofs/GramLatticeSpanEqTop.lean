import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CovTop.SpanMK

theorem span_MK_eq_top {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (_hR : RowsT p) (hG : GramAt p i) :
    Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) = ⊤ := by
  obtain ⟨ι, hι, -, himg⟩ := GlobalTheory.CovTop.SupImage.exists_emb_image_latW D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hspan := hG.2.2.2.2.2
  have hall : ∀ g, g ∈ Submodule.span p.T.Q.c.F
      (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i)) →
      ι g ∈ Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (himg ▸ ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨n, b, hbW, -, -, -, hbL⟩ := p.fw.ks i
  rw [eq_top_iff, ← hbL, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨f, hf⟩ := (p.fw.e i).surjective ⟨b k, hbW k⟩
  have hE : VK p.fw i = p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := GlobalTheory.AllWt.cuspW_wtZ _ _
  let g : VK p.fw i := ⟨f.1, hE.symm ▸ f.2⟩
  obtain ⟨h, hg⟩ := hι g
  have e1 : ι g = b k := by
    rw [hg]
    have : (⟨(g : p.T.R ((i : ℕ) + 1)), h⟩ : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = f := Subtype.ext rfl
    rw [this, hf]
  rw [← e1]
  exact hall g (hspan.ge Submodule.mem_top)

end GlobalTheory.CovTop.SpanMK
