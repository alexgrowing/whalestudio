import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumCmp

section Maps

variable {X Y X' : Scheme.{0}} (L : LB X) (L' : LB X') {J : Type} [Fintype J]

lemma mapsAtExp_le_b (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L (fun i => p ≫ pr i) jN := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : p.base y ∈ LB.wchart L pr jN := hy.1
  exact Set.mem_iInter.1 h1 i

lemma mapsAtExp_le_a (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def MapsAtExp (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAtExp_le_b L L' pr ε p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAtExp_le_a L L' pr ε p jN jL) (a.s (fun _ => jL))

end Maps

variable {R : Type} [CommRing R] [IsDomain R]

def twφ (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A) : Fin 3 → (D₀.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A β (toUnit D₀.P.A ≫ b)).left, (toUnit D₀.P.A ≫ b).left, (toUnit D₀.P.A ≫ η[D.P.A]).left]

def twε : Fin 3 → ℤ := ![1, -1, 1]

def IsTwist (D₀ D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) : Prop :=
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β.hom g.b) twε), w.IsGen ∧
      ∀ χ : D₀.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun i => D₀.xK χ ≫ twφ D₀ D β.hom g.b i) (fun i => -1 * twε i)),
        MapsAtExp D.P.L D₀.P.L (twφ D₀ D β.hom g.b) twε w (D₀.xK χ) (-1) (D₀.psi χ) t ∧
        LB.Gen.Corr D.P.L _ _ _ _ t
          (LB.mulGen D.P.L _ _ _ _ (D.psi (xe χ)) (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))

end GlobalTheory.MumCmp
