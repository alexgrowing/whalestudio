import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.FirstChernClassLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open FunctorialResolution.Blowup

namespace UpperTheory.Gal.KunnethLefschetz.G

variable {R : Type} [CommRing R]

def XX (Z : Sch R) : Sch R := Over.mk (pullback.fst Z.hom Z.hom ≫ Z.hom)

def p1 (Z : Sch R) : XX Z ⟶ Z := Over.homMk (pullback.fst Z.hom Z.hom) rfl

def p2 (Z : Sch R) : XX Z ⟶ Z := Over.homMk (pullback.snd Z.hom Z.hom) pullback.condition.symm

def dg (Z : Sch R) : Z ⟶ XX Z := Over.homMk (pullback.diagonal Z.hom) (by
  change pullback.diagonal Z.hom ≫ pullback.fst Z.hom Z.hom ≫ Z.hom = Z.hom
  rw [pullback.diagonal_fst_assoc])

def IsBl {Z W : Sch R} (π : W ⟶ XX Z) : Prop := IsBlowupAlongIdealSheaf π.left (dg Z).left.ker

def Ex {Z W : Sch R} (π : W ⟶ XX Z) : Sch R := Over.mk (pullback.fst π.left (dg Z).left ≫ W.hom)

def exI {Z W : Sch R} (π : W ⟶ XX Z) : Ex π ⟶ W := Over.homMk (pullback.fst π.left (dg Z).left) rfl

def exG {Z W : Sch R} (π : W ⟶ XX Z) : Ex π ⟶ Z := Over.homMk (pullback.snd π.left (dg Z).left) (by
  change pullback.snd π.left (dg Z).left ≫ Z.hom = pullback.fst π.left (dg Z).left ≫ W.hom
  rw [← Over.w (dg Z), ← pullback.condition_assoc, Over.w π])

theorem ex_comm {Z W : Sch R} (π : W ⟶ XX Z) : exI π ≫ π = exG π ≫ dg Z := Over.OverMorphism.ext pullback.condition

def Coord (Z : Sch R) (U : Z.left.Opens) {D : ℕ} (u : Fin D → Sec Z U) : Prop :=
  IsAffineOpen U ∧ (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] Sec Z U).toRingHom.Etale

structure DChart (Z : Sch R) (D : ℕ) where
  U : Z.left.Opens
  u : Fin D → Sec Z U
  coord : Coord Z U u
  N : (XX Z).left.Opens
  aff : IsAffineOpen N
  h1 : N ≤ (p1 Z).left ⁻¹ᵁ U
  h2 : N ≤ (p2 Z).left ⁻¹ᵁ U
  ker : RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N))).toRingHom =
    Ideal.span (Set.range fun k => secMap (p2 Z) h2 (u k) - secMap (p1 Z) h1 (u k))

def DChart.s {Z : Sch R} {D : ℕ} (c : DChart Z D) (k : Fin D) : Sec (XX Z) c.N := secMap (p2 Z) c.h2 (c.u k) - secMap (p1 Z) c.h1 (c.u k)

structure BChart {X W : Sch R} (π : W ⟶ X) (N : X.left.Opens) {D : ℕ} (s : Fin D → Sec X N) where
  V : Fin D → W.left.Opens
  aff : ∀ j, IsAffineOpen (V j)
  le : ∀ j, V j ≤ π.left ⁻¹ᵁ N
  cov : iSup V = π.left ⁻¹ᵁ N
  y : ∀ j, Fin D → Sec W (V j)
  surj : ∀ j, Function.Surjective (MvPolynomial.eval₂Hom (secMap π (le j)).toRingHom (y j))
  ker : ∀ j, RingHom.ker (MvPolynomial.eval₂Hom (secMap π (le j)).toRingHom (y j)) =
    Ideal.span (insert (MvPolynomial.X j - 1) (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k))
  inter : ∀ j k, V j ⊓ V k = W.left.basicOpen (show Γ(W.left, V j) from y j k)
  nzd : ∀ j, secMap π (le j) (s j) ∈ nonZeroDivisors (Sec W (V j))

def CoordEx : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) [SmoothOfRelativeDimension D Z.hom] (z : Z.left),
  ∃ (U : Z.left.Opens) (u : Fin D → Sec Z U), z ∈ U ∧ Coord Z U u

def DChartEx : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) [IsSeparated Z.hom],
  (∀ (U : Z.left.Opens) (u : Fin D → Sec Z U), Coord Z U u → ∀ z ∈ U, ∃ c : DChart Z D, c.U = U ∧ HEq c.u u ∧ (dg Z).left z ∈ c.N) ∧
  ∀ (c : DChart Z D) (N' : (XX Z).left.Opens), IsAffineOpen N' → ∀ h : N' ≤ c.N,
    RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N'))).toRingHom = Ideal.span (Set.range fun k => secRes (XX Z) h (c.s k))

def DCoord : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) (c : DChart Z D),
  (MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s).Etale

def BChartEx : Prop := ∀ (R : Type) [CommRing R] {X W : Sch R} (π : W ⟶ X) (I : X.left.IdealSheafData), IsBlowupAlongIdealSheaf π.left I →
  ∀ (N : X.left.affineOpens) (D : ℕ) (A : Type) [CommRing A] (φ : MvPolynomial (Fin D) A →+* Sec X N.1), φ.Flat →
    (show Ideal (Sec X N.1) from I.ideal N) = Ideal.span (Set.range fun k => φ (MvPolynomial.X k)) →
    Nonempty (BChart π N.1 fun k => φ (MvPolynomial.X k))

def BlowUpChart₂ : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} [IsSeparated Z.hom] (π : W ⟶ XX Z), IsBl π → ∀ (D : ℕ) (c : DChart Z D),
  Nonempty (BChart π c.N c.s)

def BCoord : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} (π : W ⟶ XX Z) (D : ℕ) (c : DChart Z D) (b : BChart π c.N c.s) (j : Fin D),
  (MvPolynomial.eval₂Hom ((secMap π (b.le j)).comp (secMap (p1 Z) c.h1)).toRingHom
    (Function.update (b.y j) j (secMap π (b.le j) (c.s j)))).Etale

def BlowUpOff : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
  (π : W ⟶ XX Z), IsBl π → IsProper π.left ∧ IsClosedImmersion (exI π).left ∧
    ∀ U : (XX Z).left.Opens, (U : Set (XX Z).left) = (Set.range (dg Z).left)ᶜ →
      IsIso (π.left ∣_ U) ∧ ((π.left ⁻¹ᵁ U : W.left.Opens) : Set W.left) = (Set.range (exI π).left)ᶜ

def BlowUpSmooth : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (D : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension D Z.hom] (π : W ⟶ XX Z), IsBl π →
    SmoothOfRelativeDimension D (π ≫ p1 Z).left ∧ SmoothOfRelativeDimension (D + D) W.hom

def ExChart : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} [IsSeparated Z.hom] (π : W ⟶ XX Z) (D : ℕ) (c : DChart Z D)
  (b : BChart π c.N c.s) (j : Fin D), IsAffineOpen ((dg Z).left ⁻¹ᵁ c.N) ∧ IsAffineOpen ((exI π).left ⁻¹ᵁ b.V j) ∧
    RingHom.ker (secMap (exI π) (le_refl ((exI π).left ⁻¹ᵁ b.V j))).toRingHom = Ideal.span {secMap π (b.le j) (c.s j)} ∧
    ∃ h : (exI π).left ⁻¹ᵁ b.V j ≤ (exG π).left ⁻¹ᵁ ((dg Z).left ⁻¹ᵁ c.N), Function.Bijective
      (MvPolynomial.eval₂Hom (secMap (exG π) h).toRingHom fun k : {k : Fin D // k ≠ j} => secMap (exI π) le_rfl (b.y j k))

def ExSmooth : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z), IsBl π →
    SmoothOfRelativeDimension d (exG π).left ∧ IsProper (exG π).left ∧ Surjective (exG π).left

def ExDiv : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (D : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension D Z.hom] (π : W ⟶ XX Z), IsBl π → ∃ (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)), IsDiv (exI π) L s

def Jac : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) [IsSeparated Z.hom] (D : ℕ) (c c' : DChart Z D) (N : (XX Z).left.Opens), IsAffineOpen N →
  ∀ (h : N ≤ c.N) (h' : N ≤ c'.N), ∃ g : Matrix (Fin D) (Fin D) (Sec (XX Z) N),
    (∀ k, secRes (XX Z) h' (c'.s k) = ∑ l, g k l * secRes (XX Z) h (c.s l)) ∧
    IsUnit (g.map (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N)))).det ∧
    ∀ g' : Matrix (Fin D) (Fin D) (Sec (XX Z) N), (∀ k, secRes (XX Z) h' (c'.s k) = ∑ l, g' k l * secRes (XX Z) h (c.s l)) →
      g'.map (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N))) = g.map (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N)))

def ProjProd : Prop := ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (q : Y ⟶ Sp R), IsProjOver p →
  (IsProjOver q → IsProjOver (pullback.fst p q ≫ p)) ∧ (∀ i : Y ⟶ X, IsClosedImmersion i → IsProjOver (i ≫ p)) ∧ IsProper p

def BlowUpEmbedding : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {X W : Scheme.{0}} (p : X ⟶ Sp R), IsProjOver p →
  ∀ (I : X.IdealSheafData) (π : W ⟶ X), IsBlowupAlongIdealSheaf π I → ∃ (M : ℕ) (f : W ⟶ PSpace R M) (h : π ≫ p = f ≫ PSpace.str R M),
    IsClosedImmersion (pullback.lift π f h : W ⟶ pullback p (PSpace.str R M))

def BlowUpTop : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Sch R) (d : ℕ) [SmoothOfRelativeDimension (d + 1) Z.hom],
  IsProjOver Z.hom → ∃ (W : Sch R) (π : W ⟶ XX Z), IsBl π ∧ IsProjOver (XX Z).hom ∧ IsProjOver W.hom ∧ IsProjOver (Ex π).hom ∧
    SmoothOfRelativeDimension (d + 1 + (d + 1)) (XX Z).hom ∧ SmoothOfRelativeDimension (d + 1 + (d + 1)) W.hom ∧
    SmoothOfRelativeDimension (d + (d + 1)) (Ex π).hom

def BlowUpBase : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), φ.Flat → ∀ (Z W : Sch R) (Z' W' : Sch R')
  [IsSeparated Z.hom] (a : Z'.left ⟶ Z.left), IsPullback a Z'.hom Z.hom (spMap φ) → ∀ (π : W ⟶ XX Z), IsBl π →
  ∀ (b : W'.left ⟶ W.left), IsPullback b W'.hom W.hom (spMap φ) → ∃ π' : W' ⟶ XX Z', IsBl π' ∧
    (π' ≫ p1 Z').left ≫ a = b ≫ (π ≫ p1 Z).left ∧ (π' ≫ p2 Z').left ≫ a = b ≫ (π ≫ p2 Z).left

def FinCover : Prop := ∀ (k : Type) [Field k] [CharZero k] {Z : Scheme.{0}} [IsIntegral Z] (p : Z ⟶ Sp k) (D : ℕ)
  [SmoothOfRelativeDimension D p], IsProjOver p → ∃ f : Z ⟶ PSpace k D, f ≫ PSpace.str k D = p ∧ IsFinite f ∧ Surjective f ∧
    ∃ U : (PSpace k D).Opens, Nonempty U ∧ Etale (f ∣_ U)

end UpperTheory.Gal.KunnethLefschetz.G
