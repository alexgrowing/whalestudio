import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicApproxAlgebraicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointAffineApproxStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CovHt.Link.DenseBound

theorem strHom_finiteType {F : Type} [Field F] (Y : Var F) (U : Y.X.Opens) (hU : IsAffineOpen U) :
    (HorizPt.strHom Y.str U).hom.FiniteType := by
  have h1 : (Y.str.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType Y.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of F)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2
  exact RingHom.FiniteType.comp h1 h2

theorem drAt_le_of_algPt : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (B : ℝ), 0 < B → (∀ (ι : AlgebraicClosure D.what₂.LL →+* ℂ_[p]) (y : AlgPt (Φ.C k).Y), drAt Φ k la p (spMap ι ≫ y.1) f ≤ B) → ∀ x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X, drAt Φ k la p x f ≤ B := by
  intro _ _ D A N j S κ s Φ k la f hf p _ B _ hall x
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨U, hU, ε, -, t, η, hη, hcl⟩ :=
    GlobalTheory.T.padic_point_affine_approx D A N j S κ s Φ k la f hf p x (drAt Φ k la p x f - B) (by linarith)
  letI : Algebra D.what₂.LL Γ((Φ.C k).Y.X, U) := (HorizPt.strHom (Φ.C k).Y.str U).hom.toAlgebra
  haveI : Algebra.FiniteType D.what₂.LL Γ((Φ.C k).Y.X, U) := strHom_finiteType (Φ.C k).Y U hU
  obtain ⟨ι, φ, hφ⟩ := GlobalTheory.T.padic_approx_algebraic_point D.what₂.LL Γ((Φ.C k).Y.X, U) p ε t η hη
  let y : AlgPt (Φ.C k).Y := ⟨spMap φ.toRingHom ≫ hU.fromSpec, by
    rw [Category.assoc, HorizPt.fromSpec_str, ← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a⟩
  have e : spMap ι ≫ y.1 = spMap (ι.comp φ.toRingHom) ≫ hU.fromSpec := by
    show spMap ι ≫ spMap φ.toRingHom ≫ hU.fromSpec = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have h1 := hcl (ι.comp φ.toRingHom) hφ
  have h2 := hall ι y
  rw [e] at h2
  linarith

end GlobalTheory.CovHt.Link.DenseBound
