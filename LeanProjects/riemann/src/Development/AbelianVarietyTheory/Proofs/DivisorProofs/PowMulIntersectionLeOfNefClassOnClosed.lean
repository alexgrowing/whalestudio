import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixExp

theorem pow_mul_le_of_cls_eq {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)]
    (h : Published.NefProductNonneg) (hp : IsProjOver (strHom k Y)) {e : ℕ}
    (hD : topologicalKrullDim Y = e) {N N' N₀ : LB Y} (hN : IsNef k N) (hN' : IsNef k N')
    (h₀ : N₀.IsLB) (a b : ℕ) (hc : cls N₀ h₀ = a • cls N hN.isLB + b • cls N' hN'.isLB) :
    (a : ℤ) ^ e * interNum k (structureModule Y) (fun _ : Fin e => N) ≤
      interNum k (structureModule Y) (fun _ : Fin e => N₀) := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k Y) (structureModule Y) hp
    (d := e) (by rw [suppDim_structureModule, hD])
  have hL : ∀ j, IsNef k ((![N, N'] : Fin 2 → LB Y) j) := fun j => by
    fin_cases j
    exacts [hN, hN']
  have e₁ := H.interNum_of_cls_eq_sum (L := ![N, N']) (fun j => (hL j).isLB)
    (Q := fun _ => N₀) (fun _ => h₀) (fun _ => ![(a : ℤ), (b : ℤ)])
    (fun _ => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natCast_zsmul]
      exact hc)
  have e₂ := Finset.single_le_sum
    (f := fun c : Fin e → Fin 2 =>
      (∏ i, (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) (c i)) *
        interNum k (structureModule Y) (![N, N'] ∘ c))
    (fun c _ => mul_nonneg (Finset.prod_nonneg fun i _ => by
        generalize c i = j
        fin_cases j <;> simp)
      (h.interNum_nonneg (N := ![N, N'] ∘ c) hp hD fun i => hL (c i)))
    (Finset.mem_univ fun _ => 0)
  rw [e₁]
  refine le_trans (le_of_eq ?_) e₂
  simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.MixExp

open GlobalTheory.MixExp in

theorem GlobalTheory.mixExp_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  intro h k _ X q hq
  letI := algebraΓOfHom q
  intro N N' N₀ hN hN' h₀ a b Z e hnef hnef' hc hZ
  have hp : IsProjOver (strHom k X) := by rwa [strHom_eq (f := q) fun _ => rfl]
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  change (a : ℤ) ^ e * interNumOn k (redι Z) (fun _ : Fin e => N) ≤
    interNumOn k (redι Z) (fun _ : Fin e => N₀)
  rw [interNumOn_eq_interNum_pull hi fun _ => hN, interNumOn_eq_interNum_pull hi fun _ => h₀]
  refine pow_mul_le_of_cls_eq h.1 hpZ ((topologicalKrullDim_red Z).trans hZ)
    (hnef.pull_of_isClosedImmersion (redι Z) hi) (hnef'.pull_of_isClosedImmersion (redι Z) hi)
    (LB.isLB_pull h₀ (redι Z)) a b ?_
  rw [cls_pull h₀, cls_pull hN, cls_pull hN', hc, map_add, map_nsmul, map_nsmul]
