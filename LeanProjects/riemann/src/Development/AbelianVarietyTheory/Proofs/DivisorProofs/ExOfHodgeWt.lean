import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def offCM (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) : ℤ :=
  if τ (H.rt : E) = H.rt0 then 0 else if conjEmb τ (H.rt : E) = H.rt0 then 1 else 0

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exOf_hodgeWt (Dw : Datum H) :
    GlobalTheory.AllWt.exOf Dw (hodgeWt Dw) 0 = fun ix => ix.elim 0 fun x => offCM H x.1 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · simp only [GlobalTheory.AllWt.exOf, exZ, GlobalTheory.AllWt.wtOf, Option.elim, offCM, hodgeWt, CompHt.barWt]
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h, if_pos h]
      split_ifs <;> omega
    · have hm : Dw.mult τ = Dw.q := by simp [Datum.mult, h]
      have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 hm
      simp only [dif_neg h, if_neg h]
      by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_pos h', if_pos h', dif_pos hi]
        split_ifs <;> omega
      · simp only [dif_neg h', if_neg h']

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def DetEqns (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (φ₀ : c.F →+* (X₀ TF.Y Z).functionField)
    (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι))
    (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)) : Prop :=
  ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x)
    (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField)
    (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ),
    (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧
    (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧
    (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)
      (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k)
      (A τ i) (f₀.v τ i)) ∧
    D.IsEqn x (∏ τ, d τ ^ (-a τ))

section Eqv

def EqvLin {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X) (G' : Over X)
    [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  IsGrpPullback G' t.G p ψ ∧ (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) ∧
    (∀ γ, IsGrpPullback G' G' (ρ' γ).hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    (∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁) ∧
    ∀ γ (x : X), X.fromSpecResidueField x ≫ (ρ' γ).hom = X.fromSpecResidueField x →
      ∀ (T : Scheme.{0}) (w : T ⟶ G'.left) (v : T ⟶ Spec (X.residueField x)),
        w ≫ G'.hom = v ≫ X.fromSpecResidueField x → w ≫ m γ = w

end Eqv

end GlobalTheory.HodgeLin
