import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

def TraitRed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    {B L : LB G.left} {N : ℕ} (s : Fin (N + 1) → B.Sec) (θ : L.Sec) (Y : Over (Sp (ResidueField R))) [GrpObj Y]
    (j : Y.left ⟶ PSpace R N) (O : Y.left.Opens) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (s i) (p' ≫ β)) hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → (p' ≫ β) x ∈ nonzeroLocus θ

def embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) : X.Opens := ⨆ i, nonzeroLocus (s i)

theorem iSup_nonzeroLocus_embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) :
    ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (embH s).ι) = ⊤ := by
  simp only [GlobalTheory.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

def embF {R : Type} [CommRing R] {X : Scheme.{0}} {B : LB X} {N : ℕ} (q : X ⟶ Sp R) (s : Fin (N + 1) → B.Sec) :
    (embH s).toScheme ⟶ PSpace R N :=
  GlobalTheory.ProjSpace.toProj ((embH s).ι ≫ q) (fun i => GlobalTheory.secPull (s i) (embH s).ι) (iSup_nonzeroLocus_embH s)

end GlobalTheory.Mum.SecEmb
