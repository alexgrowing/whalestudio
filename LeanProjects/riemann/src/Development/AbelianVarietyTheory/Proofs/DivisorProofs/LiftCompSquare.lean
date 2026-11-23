import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FinrankOfExpBij
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SharpIdent

theorem lift_comp_square {S S' : Scheme.{0}} {G : Over S} {G₁ G₂ T : Over S'} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G.left} {φ₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {ψ₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (hφ : IsSquare φ φ₂) (hψ : IsSquare ψ ψ₂) (x x' : T ⟶ G₁) (y y' : T ⟶ G₂) (h : x.left ≫ φ = y.left ≫ ψ)
    (h' : x'.left ≫ φ = y'.left ≫ ψ) : (lift x x').left ≫ φ₂ = (lift y y').left ≫ ψ₂ := by
  have e₁ : ((lift x x').left ≫ φ₂) ≫ (fst G G).left = ((lift y y').left ≫ ψ₂) ≫ (fst G G).left := by
    rw [Category.assoc, Category.assoc, hφ.1, hψ.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_fst, h]
  have e₂ : ((lift x x').left ≫ φ₂) ≫ (snd G G).left = ((lift y y').left ≫ ψ₂) ≫ (snd G G).left := by
    rw [Category.assoc, Category.assoc, hφ.2, hψ.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_snd, lift_snd, h']
  exact pullback.hom_ext e₁ e₂

theorem exists_iso_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))), SharpOver F W P T.y → ∀ (A8 : PolAV (Sp (FractionRing T.V)))
    (pA : IsPowPolAV A8 T.A 8), ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro g n o _ ζ F W T P hP A8 pA
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL⟩ := hP
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  refine ⟨φ, hφ, ?_⟩
  have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
    have h : φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp a
    rw [h, Over.comp_left, Category.assoc, hee]
  have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
  obtain ⟨w', hw'⟩ := T.lb
  have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
    (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
  have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
      fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
    funext fun ab => lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
  rw [hm] at i₁
  exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
    (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)

end GlobalTheory.Poinc.SharpIdent
