import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

abbrev LOne : LB Q.G.left := LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)

abbrev SecFam (N : M.Z.Opens) : Type := ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j)

abbrev ThMul (c : Ω) (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => c) _ σ

abbrev FibNe (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ N →
    ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0

abbrev ExtPt (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) : Prop :=
  h ≫ Q.G.hom = W.ι ∧
  ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = M.pt → x' ≫ Q.φ ≫ Q.G.hom = M.pt →
    x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ Q.φ

def MulRel (n : ℕ)
    (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (κ : LB.Gen (LB.LinComb Q.L.L (K := Fin 2) ![𝟙 Q.G.left, (mulA Q.G n).left] ![(n : ℤ) ^ 2, -1])) : Prop :=
  ∀ (K : Type) [Field K] (g g' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP jP' : ρ.P.L.ι) (jL jL' : Q.L.L.ι),
    g' ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left →
    g' ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ →
    Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL →
    Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP' → Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL' →
    valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (α.s ![jP, jP']).val *
        valF g' _ (Q.w.s (fun _ => jP', fun _ => jL')).val =
      valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ^ (n ^ 2) * valF (g ≫ Q.φ) _ (κ.s ![jL, jL']).val

def FrameUnit (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme) : Prop :=
  ∀ (jP : ρ.P.L.ι) (jL : Q.L.L.ι) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀) (e : Ω), h w ∈ Q.L.L.U jL →
    x' ≫ Q.φ ≫ Q.G.hom = M.pt → x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left →
    Set.range (x' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP →
    e = valF (X := (baseOver (Sp S.R)).left) (spMap S.R.val.toRingHom) _ ((ρ.fr a).s fun _ => jP).val /
      valF x' _ (Q.w.s (fun _ => jP, fun _ => jL)).val →
    e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w)

def TestFac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) : Prop :=
  (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) ∧
    spMap jV ≫ yV = y ∧ yK ≫ U₀.ι = jK u.V ≫ yV ∧ yK ≫ Q.u₀ = spMap u.yK

def TestMap {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) (F : u.G.left ⟶ Q.G.left)
    (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀) : Prop :=
  IsGrpPullback u.G Q.G yV F ∧ ψ ≫ pullback.fst _ _ = u.U.gen.hom.left ≫ u.φ ∧
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ yK ∧ ψ ≫ Q.φ = pullback.fst _ _ ≫ F

end GlobalTheory.ZH.ZHPre
end
