import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens)

def IsCoc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')

def CechFG (R : Type) [CommRing R] (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) : Prop :=
  ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, IsCoc W (e k)) ∧
    ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (r : Fin N → R) (h : ∀ i : J, Γ(Z, W i)),
      ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') + ∑ k, act i i' (r k) * e k i i'

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

def fv (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) : Γ(Z, B.1) :=
  f (Opposite.op A) (Opposite.op B) (homOfLE h).op

def gv (g : C0 (OAff s)) (A : Z.affineOpens) : Γ(Z, A.1) := g (Opposite.op A)

theorem fv_d0 (g : C0 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (d0 (OAff s) g) h = gv s g B - resG Z h (gv s g A) := rfl

theorem fv_add (f f' : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (f + f') h = fv s f h + fv s f' h := rfl

theorem fv_smul (r : R) (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (r • f) h = (secMap s B.1).hom r * fv s f h := rfl

theorem res_val (f : Z1 (OAff s)) {A B C : Z.affineOpens} (hBA : B.1 ≤ A.1) (hCB : C.1 ≤ B.1) :
    resG Z hCB (fv s f.1 hBA) = fv s f.1 (hCB.trans hBA) - fv s f.1 (A := B) hCB :=
  eq_sub_of_add_eq (f.2 (homOfLE hBA).op (homOfLE hCB).op).symm

variable (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))

def rho (f : C1 (OAff s)) (i i' : J) : Γ(Z, W i ⊓ W i') :=
  fv s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
    fv s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right

theorem rho_isCoc (hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (f : Z1 (OAff s)) :
    IsCoc W (rho W s hW hW2 f.1) := by
  intro i i' i''
  let T : Z.affineOpens := ⟨W i ⊓ W i' ⊓ W i'', hW3 i i' i''⟩
  have h1 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_left inf_le_left
  have h2 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_right inf_le_left
  have h3 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h4 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h5 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have h6 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  simp only [rho, map_sub]
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem rho_add (f f' : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (f + f') i i' = rho W s hW hW2 f i i' + rho W s hW hW2 f' i i' := by
  simp only [rho, fv_add]
  ring

theorem rho_smul (r : R) (f : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (r • f) i i' = (secMap s (W i ⊓ W i')).hom r * rho W s hW hW2 f i i' := by
  simp only [rho, fv_smul]
  ring

theorem rho_zero (i i' : J) : rho W s hW hW2 0 i i' = 0 := sub_self (0 : Γ(Z, W i ⊓ W i'))

theorem rho_sum {N : ℕ} (r : Fin N → R) (f : Fin N → C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (∑ k, r k • f k) i i' = ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * rho W s hW hW2 (f k) i i' := by
  induction N with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact rho_zero W s hW hW2 i i'
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, rho_add, rho_smul, ih]

theorem rho_d0 (g : C0 (OAff s)) (i i' : J) :
    rho W s hW hW2 (d0 (OAff s) g) i i' =
      resG Z inf_le_left (-gv s g ⟨W i, hW i⟩) - resG Z inf_le_right (-gv s g ⟨W i', hW i'⟩) := by
  simp only [rho, fv_d0, map_neg]
  ring

end GlobalTheory.CechFin
