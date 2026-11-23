import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}

open MonObj in

theorem isCombAtG_perm (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ} (p : Equiv.Perm (Fin m))
    (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left)
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t x0 (fun j => v (p j)) (fun j => cf (p j)) w := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun j => u (p j), fun j => hu (p j), ?_⟩
  rw [← hp]
  letI : CommMonoid (tEpsG x0 ⟶ t.G) := Hom.commMonoid
  exact congrArg Over.Hom.left ((List.prod_ofFn (f := fun j => u (p j))).trans
    ((Equiv.prod_comp p u).trans (List.prod_ofFn (f := u)).symm))

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def permE {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n :=
  (Equiv.sigmaCongrRight p).trans e

theorem permE_apply {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    permE e p ⟨σ, j⟩ = e ⟨σ, p σ j⟩ := rfl

def IsFrameMat (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
    IsCombAtG TF.Y.t (z ≫ toBase TF Z)
      (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
      (fun j => ev z W hz (C σ i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

variable {TF : TorFlag Xo c} {Z : Comp Xo c} {U : TF.Y.X.affineOpens} {n : ℕ}
  {e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n} {v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)}

theorem isEigBasis_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (h : IsEigBasis TF U e v) :
    IsEigBasis TF U (permE e p) v :=
  ⟨h.1, h.2.1, fun a τ i => h.2.2 a τ (p τ i)⟩

theorem isFrameMat_mono {W W₀ : (Y₀ TF.X Z).Opens} (hW : W ≤ W₀) {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀)}
    (h : IsFrameMat TF Z U e v W₀ k C) :
    IsFrameMat TF Z U e v W k (fun σ => (C σ).map (resG (Y₀ TF.X Z) hW)) := by
  intro S _ z hz hU hk hx σ i
  have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := FlagMod.le_preimage_mono hW hz
  have h1 := h S z hz₀ hU hk hx σ i
  have e1 : (fun j => ev z W₀ hz₀ (C σ i j)) = fun j => ev z W hz (((C σ).map (resG (Y₀ TF.X Z) hW)) i j) :=
    funext fun j => (FlagMod.ev_res z hW hz hz₀ _).symm
  rw [e1] at h1
  exact h1

theorem isFrameMat_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)}
    (h : IsFrameMat TF Z U e v W k C) :
    IsFrameMat TF Z U (permE e p) v W k (fun σ => (C σ).submatrix id (p σ)) := by
  intro S _ z hz hU hk hx σ i
  simp only [permE_apply, Matrix.submatrix_apply, id]
  exact isCombAtG_perm TF.Y.t (z ≫ toBase TF Z) (p σ)
    (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (fun j => ev z W hz (C σ i j))
    (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left (h S z hz hU hk hx σ i)

theorem isCell_of_isFrameMat {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)} (hW : IsAffineOpen W)
    (hWU : W ≤ toBase TF Z ⁻¹ᵁ U.1) (hWk : W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) (hL : ∀ σ i j, i < j → L σ i j = 0)
    (hLd : ∀ σ i, IsUnit (L σ i i)) (hN : ∀ σ i j, j < i → N σ i j = 0) (hNd : ∀ σ i, N σ i i = 1)
    (h : IsFrameMat TF Z U e v W k fun σ => L σ * N σ) : IsCell TF Z U e v W k L N :=
  ⟨hW, hWU, hWk, hL, hLd, hN, hNd, h⟩

end GlobalTheory.LogPole
