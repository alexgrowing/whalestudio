import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

namespace Formalism.L2.Pj.abelian₂

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped ComplexOrder
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Over.cartesianMonoidalCategory

variable {D : D7}

section Part1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

structure LamLetters (o : LamObj c nΨ n') where
  m : (E →+* ℂ) → ℕ
  e : (Σ b, Fin (m b)) ≃ Fin o.xB.P.g

  src : Fin o.xB.P.g → (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g)
  U : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁
  ℓ : Fin o.xB.P.g → MLine o.K₁

def LamLetters.IsLetter {o : LamObj c nΨ n'} (L : LamLetters o) (k : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A) : Prop :=
  match L.src k with
  | Sum.inl q => w.left ≫ o.φB = (o.xΨ.v q.2).left ≫ o.φΨg ≫ (o.φΨ q.1).left
  | Sum.inr q => w.left ≫ o.φB = (o.x'.v q.2).left ≫ o.φ'g ≫ (o.φ' q.1).left

def LamLetters.IsGood {o : LamObj c nΨ n'} (L : LamLetters o) : Prop :=
  Function.Bijective L.src ∧
  (∀ b (i : Fin (L.m b)), match L.src (L.e ⟨b, i⟩) with
    | Sum.inl q => (o.τΨ q.2 : E →+* ℂ) = b ∧ (q.1 : ℕ) = i
    | Sum.inr q => (o.τ' q.2 : E →+* ℂ) = b ∧ (q.1 : ℕ) = i) ∧
  (∀ k, ∃ w, L.IsLetter k w ∧ IsLieComb (L.U k) o.xB.v w) ∧
  ∀ k, match L.src k with
    | Sum.inl q => L.ℓ k = o.ℓΨ q.2
    | Sum.inr q => L.ℓ k = o.ℓ' q.2

end Part1

def LamDegSt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (logOm : ℝ) : Prop :=
  ∀ [StarRing (𝓞 E)] (l : Level H) (c : Coeff l),
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La →
    (∀ k, (o.ℓΨ k).ndeg = logOm / 2) ∧ ∀ k, (o.ℓ' k).ndeg = logOm / 2

def LamIndSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l),
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La →
    ∀ L : LamLetters o, L.IsGood → L.U.det ≠ 0

def LamLenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l),
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La →
    ∀ L : LamLetters o, L.IsGood → ∀ σ : o.K₁ →+* ℂ, ∃ Hm : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) ℂ,
      Hm.PosDef ∧ o.LamL.n σ = Real.sqrt Hm.det.re ∧
      ∀ k, ReciprocityTheory.MultiplicativeHeights.hq Hm (ReciprocityTheory.MultiplicativeHeights.embVec σ (L.U k)) ≤ (La * (L.ℓ k).n σ) ^ 2

def LamPtClauses (T : Formalism.L2.Pj.Core D) (j : ℕ) (La : ℝ) (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) :
    letI := T.Q.H.starRing
    ∀ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)), Prop :=
  letI := T.Q.H.starRing
  fun o L σ₁ y eY =>
    LamObjGood o D.R.f La ∧ L.IsGood ∧ (∀ b, L.m b ≤ D.R.r) ∧
    IsGrpPullback o.xB.P.A (T.Q.Xo j).univ.t.G y.x (eY.hom.left ≫ gxFst y.x) ∧

    (∃ (he : eSec o.xB.P.A ≫ eY.hom.left ≫ gxFst y.x = y.x ≫ eSec (T.Q.Xo j).univ.t.G)
      (wP : LB.Iso o.xB.P.L ((T.Q.Xo j).univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)))
      (w : LB.Iso o.xB.P.L ((PPx y.x).pull eY.hom.left)) (s' : LB.Sec ((PPx y.x).pull eY.hom.left)),
      wP.IsGen ∧ LB.Gen.Maps (LB.linCombIso wP (K := PUnit) (fun _ => eSec o.xB.P.A) (fun _ => 1)) o.xB.rig
        (rigPullOf (eY.hom.left ≫ gxFst y.x) y.x he (T.Q.Xo j).univ.t.PP.L (T.Q.Xo j).univ.t.PP.rig) ∧
      w.IsGen ∧ PullSec eY.hom.left y.s s' ∧ IsoMaps w o.xB.th s' ∧
      ∀ (a : ((T.Q.Xo j).univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)).ι) (b : ((PPx y.x).pull eY.hom.left).ι)
        (i : o.xB.P.L.ι) (pt : o.xB.P.A.left),
        pt ∈ ((T.Q.Xo j).univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)).U a → pt ∈ ((PPx y.x).pull eY.hom.left).U b →
        pt ∈ o.xB.P.L.U i →
        gm (𝟙 _) pt _ (wP.s (a, i)) =
          gm (eY.hom.left ≫ gxFst y.x) pt _ ((T.Q.Xo j).univ.t.PP.L.g (a ⟨⟩) (b ⟨⟩ 0)) *
            gm (𝟙 _) pt _ (w.s (b, i))) ∧
    (∀ a : 𝓞 D.host.E, ∃ α : o.xB.P.A ⟶ o.xB.P.A, α.left ≫ o.φB = o.φB ≫ (o.oa.act a).left ∧
      (α ≫ eY.hom).left ≫ gxFst y.x = eY.hom.left ≫ gxFst y.x ≫ ((T.Q.Xo j).univ.t.act.act a).left) ∧
    (∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), ∃ (kk : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A),
      (∃ (b : D.host.E →+* ℂ) (i' : Fin (L.m b)), b = τ ∧ (i' : ℕ) = i ∧ L.e ⟨b, i'⟩ = kk) ∧
      L.IsLetter kk w ∧ y.u τ i = (w ≫ eY.hom).left ≫ gxFst y.x) ∧
    spMap σ₁.toRingHom ≫ y.x = ((T.U j T.σ₀).un k x₀).x

def LamPtSt (T : Formalism.L2.Pj.Core D) (j : ℕ) (La : ℝ) : Prop :=
  letI := T.Q.H.starRing
  LawsCore T → InR D j →
  ∀ (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) (Xx : DataX D.host.E D.R.r)
    (hX : Xx.toData = (T.U j T.σ₀).X k),
    (∀ a ∈ D.host.AA, ∀ v ∈ Xx.L', a • v ∈ Xx.Λ) →
    ∀ lam : Fin D.R.r → Fin D.R.r → D.host.E, LamBasis Xx La (hX ▸ x₀.1) lam →
    ∃ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)),
      LamPtClauses T j La k x₀ o L σ₁ y eY

end Formalism.L2.Pj.abelian₂
