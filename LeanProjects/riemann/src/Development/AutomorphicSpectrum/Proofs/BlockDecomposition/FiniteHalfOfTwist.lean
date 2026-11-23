import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinHalfAsm

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem cptPart_le' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  unfold GlobalTheory.BCT.cptPart
  exact (Subgroup.closure_le _).mpr fun t ht => ht.1

theorem mass_inf_twCent {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (Γ : Subgroup G) (δ : G) :
    mass θ (Γ ⊓ twCent θ δ) δ = mass θ Γ δ := by
  have h1 : (Γ ⊓ GlobalTheory.BCT.twCent θ δ).subgroupOf (GlobalTheory.BCT.twCent θ δ) = Γ.subgroupOf (GlobalTheory.BCT.twCent θ δ) :=
    Subgroup.inf_subgroupOf_right _ _
  have h2 : Γ ⊓ GlobalTheory.BCT.twCent θ δ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)
      = Γ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ) := by
    rw [inf_assoc, inf_eq_right.mpr (cptPart_le' _)]
  unfold GlobalTheory.BCT.mass
  rw [h1, h2]

theorem index_rStab_orbit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K U : Subgroup G)
    (f : G → ℂ) (δ : G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G))
    (hf : ∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) (x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
  have hle : U.subgroupOf K ≤ GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk'
    rw [Subgroup.mem_subgroupOf] at hk'
    change ∀ y : K, f ((x * ↑(y * k'))⁻¹ * δ * θ (x * ↑(y * k'))) = f ((x * ↑y)⁻¹ * δ * θ (x * ↑y))
    intro y
    rw [← hf (k' : G) hk' ((x * ↑y)⁻¹ * δ * θ (x * ↑y))]
    congr 1
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_of_le hle
  exact Subgroup.FiniteIndex.index_ne_zero

theorem range_pair (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    ((ratF E a).prodMap (ratF E b)).range = (ratF E a).range.prod (ratF E b).range := by
  exact MonoidHom.range_prodMap _ _

theorem finHalfOf : FinHalfOf := by
  unfold PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf PositivityTheory.Rg.BcB.G8.Fin.DcCount PositivityTheory.Rg.BcB.G8.Fin.MassProd
    PositivityTheory.Rg.BcB.G8.Fin.RatFin PositivityTheory.Rg.BcB.G8.Fin.SuppFin PositivityTheory.Rg.BcB.G8.Fin.EulerFin
    PositivityTheory.Rg.BcB.G8.KfOC PositivityTheory.Rg.BcB.G8.FinLevel PositivityTheory.Rg.BcB.G8.FinHalf
  intro hDc hMP hRat hSupp hEuler hKf hFL E _ _ _ hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨hGood, hfin1, hfin2, hfin3⟩ := hRat E hUnr a b δ₁ δ₂ h1 h2
  obtain ⟨hsupp, hsuppG⟩ := hSupp E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨U, hUo, hUinv⟩ := hFL E hUnr a b S φ₁ φ₂ hT1 hT2
  have hKo : IsOpen (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).1.prod (hKf E b).1
  have hKc : IsCompact (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).2.prod (hKf E b).2
  have hdc := hDc (PositivityTheory.Rg.BcB.G8.Gf E a b) (PositivityTheory.Rg.BcB.G8.thP E a b)
    ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
    ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) (PositivityTheory.Rg.BcB.G8.finFn S φ₁ φ₂)
    hKo hKc hGood inf_le_right hfin1 hfin2 hfin3
    (fun x0 => index_rStab_orbit _ _ U _ _ hKc hUo hUinv (x0 : PositivityTheory.Rg.BcB.G8.Gf E a b)) hsupp
  have hdc' : PositivityTheory.Rg.BcB.G8.dcSum (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.orbFn S φ₁ φ₂ δ₁ δ₂) = _ := hdc
  have hmass : GlobalTheory.BCT.mass (PositivityTheory.Rg.BcB.G8.thP E a b) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) =
      GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.ratF E a).range ((GlobalTheory.BCT.ratF E a) δ₁) *
        GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E b) (GlobalTheory.BCT.ratF E b).range ((GlobalTheory.BCT.ratF E b) δ₂) := by
    unfold PositivityTheory.Rg.BcB.G8.gam
    rw [mass_inf_twCent, range_pair]
    exact hMP _ _ (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.thF E b) _ _ _ _
  refine ⟨hsuppG, hfin1, ?_⟩
  rw [hdc', hmass, hEuler E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2]

end GlobalTheory.CompanionTheory.FinHalfAsm

end
