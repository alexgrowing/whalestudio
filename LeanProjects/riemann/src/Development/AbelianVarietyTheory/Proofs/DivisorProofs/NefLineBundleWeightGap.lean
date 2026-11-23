import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailWeightLineNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNefStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

theorem isNef_L₀ : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  intro hPr hNN hSA E _ _ _ H Dw l Xo c TF Z hF la hla
  letI := algebraΓOfHom (str₀ TF.X Z)
  classical
  obtain ⟨-, hproj, -⟩ := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hproj
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (C.isLB a) = φ a := fun _ => rfl
  have nef0 : ∀ a, φ a = 0 → IsNef c.F (L₀ TF.X Z a) := fun a h =>
    (isNef_triv c.F _).of_cls_eq (C.isLB a) (by rw [hφ, h]; rfl)
  by_cases hN : 0 < Dw.p + Dw.q
  swap
  · refine nef0 la ?_
    have : la = 0 := funext fun τ => funext fun i => absurd i.2 (by omega)
    rw [this, map_zero]
  have key : la = _ := decomp la hla hN
  let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
  let W : (Psi H × ℕ) ⊕ (Psi H × Bool) → AllWt.Weight Dw := Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
    (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1))
  have hP : ∀ x, IsNef c.F (L₀ TF.X Z (W x)) := by
    rintro (⟨τ, k⟩ | ⟨τ, b⟩)
    · show IsNef c.F (L₀ TF.X Z (piece Dw τ k))
      unfold piece
      split_ifs with h1 h2
      · exact GlobalTheory.T.head_weight_line_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k h2
      · exact GlobalTheory.T.tail_weight_line_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k (not_lt.1 h2) h1
      · exact nef0 0 (map_zero φ)
    · cases b
      · exact (GlobalTheory.T.torus_flag_unit_weight_bundles_nef hPr hNN E H Dw l Xo c TF Z hF τ).2
      · exact (GlobalTheory.T.torus_flag_unit_weight_bundles_nef hPr hNN E H Dw l Xo c TF Z hF τ).1
  refine IsNef.of_cls_eq_sum ((Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum Finset.univ) hP
    (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
      (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat)) hA (C.isLB la) ?_
  rw [hφ]
  conv_lhs => rw [key]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_nsmul]
  rcases x with ⟨τ, k⟩ | ⟨τ, b⟩ <;> rfl

end GlobalTheory.NefWt
