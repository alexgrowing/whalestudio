import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.Mean4O

theorem mem_pull_of_mem_pull_pull {X X' G : Scheme.{0}} (B : LB X) (f : X' ⟶ X) (j' : G ⟶ X') {x : G}
    {i : ((B.pull f).pull j').ι} (h : x ∈ ((B.pull f).pull j').U i) :
    x ∈ (B.pull (j' ≫ f)).U fun _ => i PUnit.unit PUnit.unit :=
  (mem_pull (F := j' ≫ f)).2 ((mem_pull (F := f)).1 ((mem_pull (F := j')).1 h))

theorem isRatSec_pull_pull {X X' G : Scheme.{0}} [IsIntegral G] (B : LB X) (f : X' ⟶ X) (j' : G ⟶ X')
    {r : (B.pull (j' ≫ f)).ι → G.functionFieldˣ} (hr : Cartier.IsRatSec (B.pull (j' ≫ f)) r) :
    Cartier.IsRatSec ((B.pull f).pull j') fun i => r fun _ => i PUnit.unit PUnit.unit := fun a b h => by
  have ha := (mem_pull (F := j')).1 h.1
  have hb := (mem_pull (F := j')).1 h.2
  have ha' := mem_pull_of_mem_pull_pull B f j' h.1
  have hb' := mem_pull_of_mem_pull_pull B f j' h.2
  have hab : genericPoint G ∈ (B.pull (j' ≫ f)).U (fun _ => a PUnit.unit PUnit.unit) ⊓
      (B.pull (j' ≫ f)).U fun _ => b PUnit.unit PUnit.unit := ⟨ha', hb'⟩
  refine (hr _ _ hab).trans (congrArg (· * _) ?_)
  have hF (U : G.Opens) (u : Γ(G, U)ˣ) (hU : genericPoint G ∈ U) :
      ((gm (𝟙 G) (genericPoint G) U u : G.functionFieldˣ) : G.functionField) = Cartier.fnOf U hU u.val :=
    gm_val (𝟙 G) _ U hU u
  refine (hF _ _ hab).symm.trans (Eq.trans (congrArg Units.val ?_) (hF _ _ h))
  exact (gm_pull_g B (j' ≫ f) (𝟙 G) _ _ _ ha' hb').trans
    ((gm_pull_g (B.pull f) j' (𝟙 G) _ a b h.1 h.2).trans
      (gm_pull_g B f (𝟙 G ≫ j') _ _ _ ha hb)).symm

theorem Cover.induces_pull_of_comp : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} (Yv : ProjVar.Var F)
    (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp (𝓞 F)) (p' : X' ⟶ Sp (𝓞 F))
    (ar : IsArithVar p Yv.dim) (nX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (ar' : IsArithVar p' Yv.dim) (nX' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X')
    (f : X' ⟶ X) (hf : f ≫ p = p') (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ X) (j' : G ⟶ X'),
    j' ≫ f = j → ∀ (πG : G ⟶ Yv.X) [IsFinite πG] [Surjective πG]
    (pb : IsPullback j (πG ≫ Yv.str) p (spMap (algebraMap (𝓞 F) F)))
    (pb' : IsPullback j' (πG ≫ Yv.str) p' (spMap (algebraMap (𝓞 F) F)))
    (φ : Yv.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ Yv.X.fromSpecStalk (genericPoint Yv.X))
    (A : TrueGeo.Adl C Yv) (L : HermLB p) (k : ℕ),
    (@Cover.mk _ _ Yv X _ p ar nX G _ j πG pb _ _ φ φs).Induces A L k →
      (@Cover.mk _ _ Yv X' _ p' ar' nX' G _ j' πG pb' _ _ φ φs).Induces A (L.pull f hf) k := by
  intro F _ _ C Yv X X' _ _ p p' ar nX ar' nX' f hf G _ j j' hj πG _ _ pb pb' φ φs A L k h
  subst hj
  obtain ⟨r, hr, h₁, h₂, h₃⟩ := h
  refine ⟨fun i => r fun _ => i PUnit.unit PUnit.unit, isRatSec_pull_pull L.B f j' hr,
    fun i x hx => h₁ _ x (mem_pull_of_mem_pull_pull L.B f j' hx),
    fun σ z y y' i e₁ e₂ hi => ?_, fun v e y z yt i e₁ e₂ hi => ?_⟩
  · refine (h₂ σ z y (Points.PtsOver.map f hf _ y') (fun _ => i PUnit.unit PUnit.unit) e₁
      ((congrArg (· ≫ f) e₂).trans (Category.assoc _ _ _))
      (mem_pull_of_mem_pull_pull L.B f j' hi)).trans ?_
    exact congrArg (fun t => _ * Real.exp (-t)) ((L.φ _).pull_φ f hf (i PUnit.unit) y').symm
  · exact h₃ v e y z (yt ≫ f) (fun _ => i PUnit.unit PUnit.unit) e₁
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) e₂).trans (Category.assoc _ _ _)))
      fun x hx => (mem_pull (F := f)).1 (hi hx)

end GlobalTheory.Mean4O
