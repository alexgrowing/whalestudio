import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.OrbitSep

section Lin

variable {X : Scheme.{0}} [IsIntegral X] {Γ : Type} [Group Γ]

def fnAct (ρ : Γ →* Aut X) (γ : Γ) : X.functionFieldˣ →* X.functionFieldˣ :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  Units.map (GlobalTheory.functionFieldMap (ρ γ).hom).toMonoidHom

def RatLin (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB) : Prop :=
  ∃ (D : CartierDiv X) (c : Γ → X.functionFieldˣ), cls (toLB D) (isLB_toLB D) = cls L hL ∧
    (∀ γ δ, c (γ * δ) = fnAct ρ δ (c γ) * c δ) ∧
    (∀ γ x g, D.IsEqn ((ρ γ).hom x) g → D.IsEqn x (fnAct ρ γ g * (c γ)⁻¹)) ∧
    ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * (c γ)⁻¹ * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Base

variable (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

abbrev X₀ : Scheme.{0} := (barComp Y Z).toScheme

abbrev s₀ : X₀ Y Z ⟶ Sp c.F := (barComp Y Z).ι ≫ Y.s

abbrev V₀ : Scheme.{0} := (Y.j ⁻¹ᵁ barComp Y Z).toScheme

abbrev i₀ : V₀ Y Z ⟶ Xo.XF c := (Y.j ⁻¹ᵁ barComp Y Z).ι

abbrev j₀ : V₀ Y Z ⟶ X₀ Y Z := Y.j ∣_ barComp Y Z

variable {Y} in

abbrev π₀ (X : FlagCover Y) (Z : Comp Xo c) : Y₀ X Z ⟶ X₀ Y Z := X.π ∣_ barComp Y Z

variable {Y} in

theorem π₀_s₀ (X : FlagCover Y) (Z : Comp Xo c) : π₀ X Z ≫ s₀ Y Z = str₀ X Z := by
  dsimp only [π₀, s₀, str₀, inc₀, flagStr]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem j₀_ι : j₀ Y Z ≫ (barComp Y Z).ι = i₀ Y Z ≫ Y.j :=
  morphismRestrict_ι _ _

variable {Y Z} in

def ActsBy {Γ : Type} [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ Y Z)) : Prop :=
  (∀ γ, (ρ γ).hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z) ∧
    ∀ (γ : Γ) (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v : Sp R ⟶ V₀ Y Z), v ≫ i₀ Y Z = ptF y →
      v ≫ (ρ γ).hom ≫ i₀ Y Z = ptF (move Xo c (ι γ)⁻¹ y)

end Base

variable (Dw) in

def kapBase : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)

def UnipAt (I : Ideal (𝓞 E)) (γ : LevelAut Dw l) : Prop :=
  ∃ m : ℕ, ∀ x : Dw.La, ((liftLa γ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)

def NeatPrime (I : Ideal (𝓞 E)) (g r : ℕ) : Prop :=
  g.Prime ∧ Ideal.absNorm I = g ∧ (g : 𝓞 E) ∉ I ^ 2 ∧ r + 1 < g

theorem gapGe_sub_kapBase (t : ℤ) (ht : ((Dw.p + Dw.q : ℕ) : ℤ) ≤ t) : GapGe 0 (t • hodgeWt Dw - kapBase Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [Pi.sub_apply, Pi.smul_apply, hodgeWt, GlobalTheory.CompHt.barWt, kapBase, smul_eq_mul]
  push_cast at ht ⊢
  split_ifs <;> omega

theorem gapGe_hodgeWt : GapGe 0 (hodgeWt Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [hodgeWt, GlobalTheory.CompHt.barWt]
  split_ifs <;> omega

end GlobalTheory.OrbitSep
