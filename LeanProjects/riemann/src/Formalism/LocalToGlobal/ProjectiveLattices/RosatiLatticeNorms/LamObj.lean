import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM

attribute [local instance] Over.cartesianMonoidalCategory

namespace Formalism.L2.Pj.abelian₂

section pts

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

def pnsmulPt {T : Over S} : ℕ → (T ⟶ G) → (T ⟶ G)
  | 0, _ => toUnit T ≫ η[G]
  | n + 1, x => padd G (pnsmulPt n x) x

def psumPt {T : Over S} {n : ℕ} (f : Fin n → (T ⟶ G)) : T ⟶ G :=
  (List.ofFn f).foldr (fun a b => padd G a b) (toUnit T ≫ η[G])

end pts

abbrev gmap (K : Type) [Field K] [NumberField K] : Sp K ⟶ Sp (𝓞 K) := specOf (algebraMap (𝓞 K) K)

def IsFibreOf {R R' : Type} [CommRing R] [CommRing R'] (A : PolAV (Sp R)) (x : KeyIn R') (f : Sp R' ⟶ Sp R)
    (φ : x.P.A.left ⟶ A.A.left) : Prop :=
  IsGrpPullback x.P.A A.A f φ ∧ ∃ w : LB.Iso x.P.L (A.L.pull φ), w.IsGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}

structure LamObj (c : Coeff l) (nΨ n' : ℕ) : Type 1 where
  K₁ : Type
  [fK : Field K₁]
  [nfK : NumberField K₁]
  [algK : Algebra c.F K₁]
  B : PolAV (Sp (𝓞 K₁))
  oa : B.OAct (𝓞 E)
  AΨ : PolAV (Sp (𝓞 K₁))
  oaΨ : AΨ.OAct (𝓞 E)
  A' : PolAV (Sp (𝓞 K₁))
  oa' : A'.OAct (𝓞 E)
  φΨ : Fin nΨ → (AΨ.A ⟶ B.A)
  φ' : Fin n' → (A'.A ⟶ B.A)
  hΨ : Fin nΨ → 𝓞 E
  h' : Fin n' → 𝓞 E
  xB : KeyIn K₁
  xΨ : KeyIn K₁
  x' : KeyIn K₁
  φB : xB.P.A.left ⟶ B.A.left
  φΨg : xΨ.P.A.left ⟶ AΨ.A.left
  φ'g : x'.P.A.left ⟶ A'.A.left
  τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}
  τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}
  ℓΨ : Fin xΨ.P.g → MLine K₁
  ℓ' : Fin x'.P.g → MLine K₁
  Tl : MLine K₁
  LamL : MLine K₁

attribute [instance] LamObj.fK LamObj.nfK LamObj.algK

def IsLieType {K : Type} [Field K] [NumberField K] {S : Set (E →+* ℂ)} (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E))
    (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) : Prop :=
  ∀ (a : 𝓞 E) (i : Fin x.P.g), ∃ w : epsR K ⟶ x.P.A,
    IsLieComb (Pi.single i (lab (τ i) (a : E))) x.v w ∧ (x.v i).left ≫ φ ≫ (oa.act a).left = w.left ≫ φ

def RosatiConj {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) : Prop :=
  ∀ (a : 𝓞 E) (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x z : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
    pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k z = toUnit Tb ≫ η[A.A] →
    (WeilIs A.A A.L k (x ≫ oa.act a) z c ↔ WeilIs A.A A.L k x (z ≫ oa.act (star a)) c)

def psiSet (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}

def labK (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (τ : E →+* ℂ) : E →+* K₁ :=
  (algebraMap c.F K₁).comp (embF c τ)

def IsModelAt {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left)
    (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : Algebra R K)
    (_ : IsFractionRing R K) (ρ : 𝓞 K →+* R) (xR : KeyIn R) (φR : xR.P.A.left ⟶ A.A.left) (hg : xR.P.g = x.P.g),
    (algebraMap R K).comp ρ = algebraMap (𝓞 K) K ∧ (∀ y : K, y ∈ Set.range (algebraMap R K) ↔ p.valuation K y ≤ 1) ∧
    IsFibreOf A xR (specOf ρ) φR ∧ M.det ≠ 0 ∧
    ∀ k, ∃ wK : epsR K ⟶ x.P.A, IsLieComb (M k) x.v wK ∧
      wK.left ≫ φ = spMap (dualMap (algebraMap R K)) ≫ (xR.v (k.cast hg.symm)).left ≫ φR

def IsVecLine {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left)
    (i : Fin x.P.g) (ℓ : MLine K) : Prop :=
  ℓ.Good ∧
  (∀ p : HeightOneSpectrum (𝓞 K), ∃ (M : Matrix (Fin x.P.g) (Fin x.P.g) K) (cl : K),
    IsModelAt A x φ p M ∧ IsLocGen p cl ℓ.I ∧
    ∀ c : K, (∀ m, p.valuation K ((c • Matrix.vecMul (Pi.single i 1) M⁻¹) m) ≤ 1) ↔
      p.valuation K c ≤ p.valuation K cl) ∧
  ∀ σ : K →+* ℂ, ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ)
      (χ : u.Λ → ℂ) (W : Fin xσ.P.g → ℂ) (hg : xσ.P.g = x.P.g),
    KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsDiff W (xσ.v (i.cast hg.symm)) ∧
    ℓ.n σ ^ 2 = Real.pi * (W ⬝ᵥ Hm.mulVec (star W)).re

variable {c : Coeff l} {nΨ n' : ℕ}

def IsIsogSum (o : LamObj c nΨ n') : Prop :=
  (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
  ∃ (N : ℕ) (ψΨ : Fin nΨ → (o.B.A ⟶ o.AΨ.A)) (ψ' : Fin n' → (o.B.A ⟶ o.A'.A)), 0 < N ∧
    (∀ (Tb : Over (Sp (𝓞 o.K₁))) (x : Tb ⟶ o.B.A),
      padd o.B.A (psumPt fun i => x ≫ ψΨ i ≫ o.φΨ i) (psumPt fun i => x ≫ ψ' i ≫ o.φ' i) = pnsmulPt N x) ∧
    (∀ (Tb : Over (Sp (𝓞 o.K₁))) (a : Fin nΨ → (Tb ⟶ o.AΨ.A)) (a' : Fin n' → (Tb ⟶ o.A'.A)),
      (∀ i, padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) ≫ ψΨ i = pnsmulPt N (a i)) ∧
      ∀ i, padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) ≫ ψ' i = pnsmulPt N (a' i))

def PolClause (o : LamObj c nΨ n') : Prop :=
  (∀ i, star (o.hΨ i) = o.hΨ i) ∧ (∀ i, star (o.h' i) = o.h' i) ∧
  (∀ i (Tb : Over (Sp (𝓞 o.K₁))) (k : ℕ) (x y : Tb ⟶ o.AΨ.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
    pnsmulPt k x = toUnit Tb ≫ η[o.AΨ.A] → pnsmulPt k y = toUnit Tb ≫ η[o.AΨ.A] →
    (WeilIs o.B.A o.B.L k (x ≫ o.φΨ i) (y ≫ o.φΨ i) c ↔ WeilIs o.AΨ.A o.AΨ.L k (x ≫ o.oaΨ.act (o.hΨ i)) y c)) ∧
  ∀ i (Tb : Over (Sp (𝓞 o.K₁))) (k : ℕ) (x y : Tb ⟶ o.A'.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
    pnsmulPt k x = toUnit Tb ≫ η[o.A'.A] → pnsmulPt k y = toUnit Tb ≫ η[o.A'.A] →
    (WeilIs o.B.A o.B.L k (x ≫ o.φ' i) (y ≫ o.φ' i) c ↔ WeilIs o.A'.A o.A'.L k (x ≫ o.oa'.act (o.h' i)) y c)

def LamBound (o : LamObj c nΨ n') (La : ℝ) : Prop :=
  (∀ i (τ : E →+* ℂ), ‖τ (o.hΨ i : E)‖ ≤ La ^ 2) ∧ ∀ i (τ : E →+* ℂ), ‖τ (o.h' i : E)‖ ≤ La ^ 2

def LamObjGood (o : LamObj c nΨ n') (f : ℕ) (La : ℝ) : Prop :=
  RosatiConj o.B o.oa ∧ RosatiConj o.AΨ o.oaΨ ∧ RosatiConj o.A' o.oa' ∧
  IsFibreOf o.B o.xB (gmap o.K₁) o.φB ∧ IsFibreOf o.AΨ o.xΨ (gmap o.K₁) o.φΨg ∧ IsFibreOf o.A' o.x' (gmap o.K₁) o.φ'g ∧
  o.xΨ.P.g = f ∧ o.x'.P.g = f ∧ o.xB.P.g = f * (nΨ + n') ∧
  IsLieType o.AΨ o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ (labK c o.K₁) ∧
  IsLieType o.A' o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' (labK c o.K₁) ∧
  (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
  (∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a) ∧
  IsIsogSum o ∧ PolClause o ∧ LamBound o La ∧
  (∀ i, IsVecLine o.AΨ o.xΨ o.φΨg i (o.ℓΨ i)) ∧ (∀ i, IsVecLine o.A' o.x' o.φ'g i (o.ℓ' i)) ∧
  o.Tl.Good ∧ o.LamL.Good ∧ (∀ p, KeyLocAt o.xB o.Tl o.LamL p) ∧ (∀ σ, KeyArchAt o.xB o.Tl o.LamL σ) ∧
  ∀ p, ∃ M, IsModelAt o.B o.xB o.φB p M ∧ IsLocGen p M.det o.LamL.I

end Formalism.L2.Pj.abelian₂
