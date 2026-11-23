import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBLit

abbrev Qb : Type := AlgebraicClosure ℚ

def IsSemiStable {S : Scheme.{0}} (G : Over S) [GrpObj G] : Prop :=
  IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S), ∃ (G₀ : Over (Spec (.of Ω))) (_ : GrpObj G₀)
      (j : G₀ ⟶ (Over.pullback p).obj G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Nonempty (TorusExtension G₀)

def InK {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((Out.translDiff A M x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen

section CubicalWeight

variable {k : Type} [CommRing k] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {M : RigLB G} {σ : k →+* ℂ}

def IsCubist (c : CubicalStr G M) (Φ : Weight G.hom σ M.L) : Prop :=
  Φ.IsCInf ∧
  (∀ (j : PUnit → M.L.ι) (y : CxPts (𝟙_ (Over (Sp k))).hom σ), y ∈ ptsIn _ σ ((M.L.pull (eSec G)).U j) →
    Real.log (‖ev _ σ _ (M.rig.s j).val y‖ ^ 2) = Φ.φ (j PUnit.unit) (PtsOver.map (eSec G) (Over.w _) _ y)) ∧
  ∀ (j : (Theta G M.L).ι) (y : CxPts (G3 G).hom σ), y ∈ ptsIn _ σ ((Theta G M.L).U j) →
    Real.log (‖ev _ σ _ (c.t.s j).val y‖ ^ 2) =
      ∑ I : thK, (thε I : ℝ) * Φ.φ (j I) (PtsOver.map (thφ G (x3 G) I) (Over.w _) _ y)

omit [IsCommMonObj G] in

def addPt (x y : CxPts G.hom σ) : CxPts G.hom σ :=
  ⟨((Over.homMk x.1 x.2 : Over.mk (spMap σ) ⟶ G) * Over.homMk y.1 y.2).left, Over.w _⟩

omit [IsCommMonObj G] in

def IsHaar (ν : Measure (CxPts G.hom σ)) : Prop := IsProbabilityMeasure ν ∧ ∀ x, ν.map (addPt x) = ν

omit [GrpObj G] [IsCommMonObj G] in

def prodAt {L : LB G.left} (Φ : Weight G.hom σ L) (s t : L.Sec) (y : CxPts G.hom σ) : ℂ :=
  starRingEnd ℂ (ev _ σ _ (s.f (pick Φ.isLB y)) y) * ev _ σ _ (t.f (pick Φ.isLB y)) y *
    (Real.exp (-Φ.φ (pick Φ.isLB y) y) : ℝ)

end CubicalWeight

structure Model (A : Over (Sp Qb)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] [NumberField K] (e : K →+* Qb) :
    Type 1 where

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiStable G

  i : A.left ⟶ G.left
  fib : IsGrpPullback A G (spMap (e.comp (algebraMap (𝓞 K) K))) i

  M : RigLB G

  cub : CubicalStr G M

  Φ : ∀ σ : K →+* ℂ, Weight G.hom (σ.comp (algebraMap (𝓞 K) K)) M.L
  isCubical : ∀ σ, IsCubist cub (Φ σ)
  conj : ∀ σ, (Φ σ).IsConj (Φ ((starRingEnd ℂ).comp σ))

  w : LB.Iso (M.L.pull i) L
  gen : w.IsGen
  ker : ∃ (Z : Scheme.{0}) (ζ : Z ⟶ G.left), IsImmersion ζ ∧ IsFinite (ζ ≫ G.hom) ∧ Flat (ζ ≫ G.hom) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Qb) (x : Over.mk t ⟶ A),
      InK A (lbPow L 2) x ↔ ∃ y : Sp R ⟶ Z, y ≫ ζ = x.left ≫ i

attribute [instance] Model.grp Model.comm

namespace Model

variable {A : Over (Sp Qb)} [GrpObj A] {L : LB A.left} {K : Type} [Field K] [NumberField K] {e : K →+* Qb}

def IsExt {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] {e' : K' →+* Qb} (m : Model A L K e)
    (m' : Model A L K' e') : Prop :=
  ∃ j : m'.G.left ⟶ m.G.left, IsGrpPullback m'.G m.G (spMap (algebraMap (𝓞 K) (𝓞 K'))) j ∧ m'.i ≫ j = m.i ∧
    LBIso (m.M.L.pull j) m'.M.L

def IsSections (m : Model A L K e) {r : ℕ} (b : Fin r → m.M.L.Sec) (E : Submodule (𝓞 K) (Fin r → K))
    (h : HermFam K (Fin r → K)) : Prop :=
  (∀ t : m.M.L.Sec, ∃! c : Fin r → K, secPull t m.i = secComb A.hom (fun a => e (c a)) fun a => secPull (b a) m.i) ∧
  (∀ c, c ∈ E ↔ ∃ t : m.M.L.Sec, secPull t m.i = secComb A.hom (fun a => e (c a)) fun a => secPull (b a) m.i) ∧
  ∀ σ : K →+* ℂ, ∃ ν : Measure (CxPts m.G.hom (σ.comp (algebraMap (𝓞 K) K))), IsHaar ν ∧
    ∀ a a', h.form σ (Pi.single a 1) (Pi.single a' 1) = ∫ y, prodAt (m.Φ σ) (b a) (b a') y ∂ν

end Model

def IsFaltings (A : Over (Sp Qb)) [GrpObj A] (g : ℕ) (x : ℝ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* Qb) (B : Over (Sp K)) (_ : GrpObj B) (a : A.left ⟶ B.left)
    (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (φ : B.left ⟶ G.left) (v : Fin g → (epsR K ⟶ B)) (h : HermFam K (Fin g → K)),
    IsGrpPullback A B (spMap e) a ∧ IsSemiStable G ∧ IsGrpPullback B G (spMap (algebraMap (𝓞 K) K)) φ ∧ IsLieBasis v ∧
    (∀ σ : K →+* ℂ, ∃ (Q : Over (Sp ℂ)) (_ : GrpObj Q) (ψ : Q.left ⟶ B.left) (N : LB Q.left) (u : HolUnif Q N g)
      (v' : Fin g → (epsR ℂ ⟶ Q)) (W : Matrix (Fin g) (Fin g) ℂ) (D : Set (Fin g → ℂ)),
      IsGrpPullback Q B (spMap σ) ψ ∧ (∀ i, IsVecOver σ ψ (v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
      IsAddFundamentalDomain u.Λ D volume ∧
      (h.gram σ fun i => Pi.single i 1).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 / (volume D).toReal) ∧
    x = -deg h (Submodule.span (𝓞 K)
      {c | ∃ u : epsR (𝓞 K) ⟶ G, IsTangent u ∧ ∃ w, IsVecOver (algebraMap (𝓞 K) K) φ u w ∧ IsLieComb c v w})

end GlobalTheory.MBLit

end
