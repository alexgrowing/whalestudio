import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Curve0 (H : Host E) (ρ : ℂ) : Type 1 where
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  ω : 𝓞 M
  C : Ell H (𝓞 M) ω
  hω : 2 * ((ω : M) : ℂ) - 1 = ρ
  C' : Ell H ℂ ((ω : M) : ℂ)
  π : C'.P.A.left ⟶ C.P.A.left
  map : EllMap C' C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) π
  u : HolUnif C'.P.A C'.P.L C'.P.g
  theta : PureType.IsThetaUnif u
  c : ℂ
  c_ne : c ≠ 0
  lat : PureType.IsQuadLattice u.Λ H.d c
  z : ℂ
  diff : u.IsDiff (fun _ => c * z) C'.v

attribute [instance] Curve0.nf

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

structure CMPack (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (c : Coeff l) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    {P : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) : Type 1 where
  K : IntermediateField ℚ ℂ
  [nf : NumberField K]
  hc : c.F ≤ K
  hM : ∀ b, (Z b).M ≤ K
  ω : Bool → 𝓞 K
  C : ∀ b, Ell H (𝓞 K) (ω b)
  φ : ∀ b, (C b).P.A.left ⟶ (Z b).C.P.A.left
  map : ∀ b, EllMap (C b) (Z b).C (RingOfIntegers.mapRingHom (IntermediateField.inclusion (hM b)).toRingHom) (φ b)
  π : ∀ b, (Z b).C'.P.A.left ⟶ (C b).P.A.left
  map' : ∀ b, EllMap (Z b).C' (C b) ((algebraMap K ℂ).comp (algebraMap (𝓞 K) K)) (π b)
  tri : ∀ b, π b ≫ φ b = (Z b).π
  ε : Bool → ℤˣ
  sgn : ∀ b, 0 < ((ε b : ℤ) : ℝ) * (sgnRt H b).im
  h : Bool → (FU.Di i).La → (FU.Di i).La → OK H
  kform : ∀ b, IsKForm (FU.Di i) (ε b) (h b)
  B : PAT H (Sp (𝓞 K))
  dim : B.g = g
  y : Sp K ⟶ Xo.XF c
  hy : y ≫ pullback.snd _ _ = spMap (IntermediateField.inclusion hc).toRingHom
  pt : spMap (algebraMap K ℂ) ≫ under y = FU.u i P
  t : SAB H (Sp K)
  m : SABMap t Xo.univ.t (under y)
  m' : SABMap t B.t (spMap (algebraMap (𝓞 K) K))
  ψ : ∀ b : Bool, PureType.lat hP (sgnRt H b) → ((C b).P.A ⟶ B.t.G)
  fam : ∀ b, IsFam (C b) B (fun x x' => h b x x') _ (ψ b)
  tie : ∀ b a (s : ℂ) (x : Sp ℂ ⟶ t.G.left), x ≫ t.G.hom = spMap (algebraMap K ℂ) →
    x ≫ m'.φ = ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i P (s • P a)).left

attribute [instance] CMPack.nf

namespace CMPack

variable {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {c : Coeff l} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P} (X : CMPack Z c FU i hP)

abbrev β : c.F →+* X.K := (IntermediateField.inclusion X.hc).toRingHom

def IsImage (b : Bool) (a : PureType.lat hP (sgnRt H b)) (u : epsAt (under X.y) ⟶ Xo.univ.t.G) : Prop :=
  ∃ r : Sp (DualNumber X.K) ⟶ X.t.G.left, r ≫ X.m.φ = u.left ∧
    r ≫ X.m'.φ = spMap (dualMap (algebraMap (𝓞 X.K) X.K)) ≫ (X.C b).v.left ≫ (X.ψ b a).left

def IsCMVec (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b))
    (v : epsAt (under X.y) ⟶ Xo.univ.t.G) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (u : Fin n → (epsAt (under X.y) ⟶ Xo.univ.t.G)),
    (∀ k, X.IsImage b (RingOfIntegers.basis E (e k) • a) (u k)) ∧
      IsComb (fun k => X.β (tauE c τ (HT.dualInt E (e k)))) u v

def IsCMFrame (τ : E →+* ℂ) {x : Fin D.p ⊕ Fin D.q → (FU.Di i).La} (hx : IsPure hP x) (v : Vecs X.y D.p)
    (w : Vecs X.y D.q) : Prop :=
  (∀ a, X.IsCMVec true τ ⟨x (.inl a), hx.1 a⟩ (v a)) ∧
    ∀ j, X.IsCMVec false (ComplexEmbedding.conjugate τ) ⟨x (.inr j), hx.2 j⟩ (w j)

end CMPack

end GlobalTheory.CompanionTheory.Ar.Fl
