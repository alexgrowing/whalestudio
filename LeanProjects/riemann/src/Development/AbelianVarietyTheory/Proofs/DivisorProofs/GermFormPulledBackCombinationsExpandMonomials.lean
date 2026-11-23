import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem eval₂_expand {Rg S : Type} [CommRing Rg] [CommRing S] (mA mB : ℕ)
    (ψ : MvPolynomial (Fin (mA * mB)) Rg →+* S) (β : Fin mA → S) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial.eval₂Hom (ψ.comp MvPolynomial.C)
        (fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * β i) F =
      MvPolynomial.eval₂Hom ψ β (expand mA mB F) := by
  rw [expand, ← MvPolynomial.coe_eval₂Hom (MvPolynomial.C.comp MvPolynomial.C), ← RingHom.comp_apply,
    MvPolynomial.comp_eval₂Hom]
  congr 1
  ext r <;> simp

theorem expand_isHomogeneous {Rg : Type} [CommRing Rg] (mA mB : ℕ) {F : MvPolynomial (Fin mB) Rg} {d : ℕ}
    (hF : F.IsHomogeneous d) : (expand mA mB F).IsHomogeneous d := by
  have h := hF.eval₂ (τ := Fin mA)
    (MvPolynomial.C.comp MvPolynomial.C : Rg →+* MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg))
    (fun j => ∑ i : Fin mA, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i)
    (fun r => MvPolynomial.isHomogeneous_C _ _)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [expand] using h

theorem germ_eval_comb : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  intro Rg _ A₀ T X f N mA mB a g φ p _ d F hF z q hq
  have hT : p z ∈ (⊤ : T.Opens) := trivial
  let ψ : MvPolynomial (Fin (mA * mB)) Rg →+* X.presheaf.stalk z :=
    (MapIff.gsH p z ⊤ hT).comp (ringOf g)
  have hC : ψ.comp MvPolynomial.C = gc (p ≫ g ≫ affπ Rg (mA * mB)) z := by
    ext r
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg (mA * mB)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [ψ, RingHom.comp_apply, ringOf, gc, MapIff.gsH, RingHom.coe_comp, Function.comp_apply]
    rw [n2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    rfl
  have hcomb : comb a φ p (matOf g) z q =
      fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * gs φ z (N.U q) ((a i).f q) := by
    funext j
    simp only [comb, ψ, RingHom.comp_apply, ringOf_X, matOf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MapIff.gsH_apply]
  rw [← hC, hcomb, eval₂_expand, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hd : ∑ i, ν i = d := by
    have := expand_isHomogeneous mA mB hF (MvPolynomial.mem_support_iff.1 hν)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  have hp : gs φ z (N.U q) (∏ i, (a i).f q ^ ν i) = ∏ i, gs φ z (N.U q) ((a i).f q) ^ ν i := by
    rw [← MapIff.gsH_apply φ z _ hq, map_prod]
    simp only [map_pow, MapIff.gsH_apply]
  simp only [ψ, RingHom.comp_apply, monSec, if_pos hd]
  rw [MapIff.gsH_apply]
  exact congrArg (fun x => gs p z ⊤ (ringOf g (MvPolynomial.coeff ν (expand mA mB F))) * x) hp.symm

end GlobalTheory.FormsLocus
