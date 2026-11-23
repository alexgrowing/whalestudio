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

namespace GlobalTheory.LogKSDiv

open TopForm

section Pair

variable {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}

def topPair (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) : Forms α n →ₗ[A] A :=
  letI := α.toAlgebra
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)))

end Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev PairIx (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) : Type :=
  Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Fin (Dw.mult τ.1) × Fin (Dw.mult ((starRingEnd ℂ).comp τ.1))

def symPair {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : PairIx H Dw) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b =>
    (if a = e ⟨P.1.1, P.2.1⟩ ∧ b = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ then 1 else 0) +
      (if a = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ b = e ⟨P.1.1, P.2.1⟩ then 1 else 0)

abbrev genPt (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z :=
  (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))

abbrev GenDer (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Type :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField

def GenKS (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left))
    (D : Fin Dw.dim → GenDer TF Z) : Prop :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (ε : Fin Dw.dim ≃ PairIx H Dw)
    (Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U),
    spMap ρ ≫ LogKS.chart U = genPt TF Z ≫ (barComp TF.Y Z).ι ∧
    (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    (∀ τ i, w τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧
    (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (Dl j).1 (symPair e (ε j))) ∧
    ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r)

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

open TopForm

theorem topPair_dForm {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) (f : Fin n → A) :
    topPair α D (dForm α f) = (Matrix.of fun i j => (letI := α.toAlgebra; (D j : Derivation k A A)) (f i)).det := by
  letI := α.toAlgebra
  rw [dForm_eq, topPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of _) = _
  congr 1
  ext i j
  exact Derivation.liftKaehlerDifferential_comp_D (D j) (f i)

end GlobalTheory.LogKSDiv
