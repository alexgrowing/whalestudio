import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

structure ZHPre {S : ThetaSys o Ω} (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) where
  u₀ : U₀.toScheme ⟶ Sp S.R
  u₀_gen : ∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap S.R.val.toRingHom
  G : Over M.Z
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G
  dim : SmoothOfRelativeDimension S.g G.hom
  qproj : IsQProjOver (G.hom ≫ M.s)
  φ : pullback ρ.P.A.hom u₀ ⟶ G.left
  cart : IsGrpPullback ((Over.pullback u₀).obj ρ.P.A) G U₀.ι φ
  L : RigLB G
  cub : CubicalStr G L
  sym : L.IsSymmetric
  w : LB.Iso (L.L.pull φ) (ρ.P.L.pull (pullback.fst ρ.P.A.hom u₀))
  w_gen : w.IsGen
  w_rig : ∀ (K : Type) [Field K] (g : Sp K ⟶ pullback ρ.P.A.hom u₀) (x : Sp K ⟶ M.Z) (y : Sp K ⟶ Sp S.R)
    (jP : ρ.P.L.ι) (jL : L.L.ι), g ≫ φ = x ≫ eSec G → g ≫ pullback.fst _ _ = y ≫ eSec ρ.P.A →
    Set.range (g ≫ pullback.fst ρ.P.A.hom u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ φ) ⊆ L.L.U jL →
    valF y _ (ρ.rig.s (fun _ => jP)).val =
      valF g _ (w.s (fun _ => jP, fun _ => jL)).val * valF x _ (L.rig.s (fun _ => jL)).val
  split : ∀ z : M.Z, ∃ E : SplitExt (Sp (M.Z.residueField z)),
    E.IsGt ((Over.pullback (M.Z.fromSpecResidueField z)).obj G)
attribute [instance] ZHPre.grp ZHPre.comm
namespace ZHPre
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def Sec : Prop := ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), z ∈ W ∧ h ≫ Q.G.hom = W.ι ∧
  ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = M.pt → x' ≫ Q.φ ≫ Q.G.hom = M.pt →
    x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ Q.φ

def LocTheta : Prop := ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : LB.Sec (Q.L.L.pull (Q.G.hom ⁻¹ᵁ N).ι)), z ∈ N ∧
  ∀ z' ∈ N, ∃ x ∈ nonzeroLocus σ, Q.G.hom ((Q.G.hom ⁻¹ᵁ N).ι x) = z'

def SecO (EE : M.Lat S.J) : Prop := ∀ (W : M.Z.Opens) (b : Matrix S.J S.J Ω), IsAffineOpen W →
  (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range b)) →
  ∃ (O : LB (Q.G.hom ⁻¹ᵁ W).toScheme) (τ : S.J → LB.Sec O), O.IsLB ∧ ⨆ i, nonzeroLocus (τ i) = ⊤ ∧
    (∀ (K : Type) [Field K] (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (g' : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι) (jO : O.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt → g' ≫ (Q.G.hom ⁻¹ᵁ W).ι = g ≫ Q.φ →
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range g' ⊆ O.U jO →
      ∃ c : K, c ≠ 0 ∧ ∀ i, ∑ l, β (b i l) * valF r _ ((ρ.s l).f (fun _ => jP)) = c * valF g' _ ((τ i).f jO)) ∧
    (∀ z ∈ W, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧
      ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme) (j : O.ι), g ≫ (Q.G.hom ⁻¹ᵁ W).ι ≫ Q.G.hom = x →
        ∑ i, c i * valF g _ ((τ i).f j) = 0) → c = 0) ∧
    ((W : Set M.Z) ⊆ abLocus Q.G → RelAmple (Over.mk (Q.G.hom ∣_ W)) O)

def Ab : Prop := abLocus Q.G = {z | S.TT M z = ⊥} ∧
  ∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → IsProper (pullback.snd Q.G.hom W.ι)
end ZHPre
end GlobalTheory.ZH
end
