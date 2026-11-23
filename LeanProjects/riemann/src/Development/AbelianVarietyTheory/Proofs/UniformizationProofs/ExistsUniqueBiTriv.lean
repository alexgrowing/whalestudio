import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.EvenCub

section Alg
variable {A A' B U : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommGroup U]

def diff₃ (k : A → U) (x y u : A) : U :=
  k (x * y * u) * (k (x * y))⁻¹ * (k (x * u))⁻¹ * (k (y * u))⁻¹ * k x * k y * k u * (k 1)⁻¹

def diffQ (k : A → U) (x a : A) : U := k (x * a) * (k x)⁻¹ * (k x)⁻¹ * (k a)⁻¹ * k 1 * k 1

def diffS (k : A → U) (x : A) : U := k x⁻¹ * (k x)⁻¹

def cubeDefect (θ : A → A → A → U) (υ : A → U) (x y u a b d : A) : U :=
  θ (x * y) u (a * b * d) * θ (x * y) (a * b) d * θ u (a * b) d * θ x y d * θ u a b * υ (x * y) * υ (x * u) *
    υ (y * u) * (θ x u (a * d) * θ x a d * θ u a d * θ y u (b * d) * θ y b d * θ u b d * θ x y u * υ (x * y * u) *
      υ x * υ y * υ u)⁻¹

def evenDefect (σ υ : A → U) (x a : A) : U := υ x⁻¹ * σ x * σ x * σ a * (σ (x * a) * υ x)⁻¹

end Alg

section Rep
variable {S X : Scheme.{0}} {L : LB X} {Y : Over S}

def Rep (L : LB X) (Y : Over S) (F : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J

variable {F F' : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U}
  {v v' : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ}

theorem Rep.mul (h : Rep L Y F v) (h' : Rep L Y F' v') :
    Rep L Y (fun U _ k => F U k * F' U k) (fun T σ z J => v T σ z J * v' T σ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ k => DVR.prod_sum₂ _ (hF U k) (hF' U k), fun T σ z J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T σ z J hJ) (hv' T σ z J hJ))⟩

theorem Rep.inv (h : Rep L Y F v) : Rep L Y (fun U _ k => (F U k)⁻¹) (fun T σ z J => (v T σ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ k => ?_, fun T σ z J hJ =>
    (val_inv _ _).trans (congrArg (·⁻¹) (hv T σ z J hJ))⟩
  show _ = (F U k)⁻¹
  rw [← hF U k, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun a _ => zpow_neg _ _

theorem Rep.pull {K : Type} [Fintype K] {Y' : Over S} {φ : K → (Y'.left ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ Y')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (p.left ≫ φ k) ^ ε k = F U h) :
    Rep L Y F (fun _ σ z J => val t (σ ≫ p).left z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, hF,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem Rep.exists_gen (hL : L.IsLB) (h : Rep L Y F v) {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = ∏ k, h (φ k) ^ ε k) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J := by
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h
  obtain ⟨t, ht, hv⟩ := Geo.Tor.exists_gen hL (φ' := φ) (ε' := ε) (fun U _ k => (hF' U k).trans (hF U k)) t' ht'
  exact ⟨t, ht, fun T σ z J hJ => (hv _ _ z J hJ).trans (hv' T σ z J hJ)⟩

theorem Rep.eq_one (hL : L.IsLB) (hY : Function.Surjective Y.hom.appTop.hom) (h : Rep L Y F v)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = 1) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → v _ e z J = 1) (T : Over S) (σ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    v T σ z J = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, hF', hv⟩ := h
  refine (hv T σ z J hJ).symm.trans ((gen_unique' hL (fun U _ k => ?_) Y.hom e.left (Over.w e) hY ht
    (LB.isGen_oneGen L) (fun y I hI => (hv _ e y I hI).trans ((he y I hI).trans (val_one _).symm)) _ σ.left z J hJ).trans
    (val_one _))
  rw [hF', hF]
  exact Fintype.prod_empty _

end Rep

section Quad
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

abbrev quadφ (w : G ⟶ G) : Fin 4 → (G.left ⟶ G.left) :=
  ![(𝟙 G * w).left, 𝟙 G.left, w.left, (1 : G ⟶ G).left]

def postHom {H : Over S} [GrpObj H] (i : H ⟶ G) [IsMonHom i] (T : Over S) : (T ⟶ H) →* (T ⟶ G) :=
  MonoidHom.mk' (· ≫ i) fun _ _ => MonObj.mul_comp _ _ _

def QuadId (P : CP G) (w : G ⟶ G) (u : LB.Gen (LB.LinComb P.L.L (quadφ w) ![1, -2, -1, 2])) : Prop :=
  ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J →
    (∀ x y v : T ⟶ G, cubeDefect (cubV P.c z J) (fun p => val u p.left z J) x y v (x ≫ w) (y ≫ w) (v ≫ w) = 1) ∧
    ∀ x : T ⟶ G, evenDefect (fun p : T ⟶ G => val P.sym p.left z J) (fun p => val u p.left z J) x (x ≫ w) = 1

variable {H : Over S} [GrpObj H] [IsCommMonObj H] {P : CP G} {i : H ⟶ G} [IsMonHom i]

end Quad

section DVR
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] [IsSeparated G.hom] [GeometricallyConnected G.hom]

end DVR

end GlobalTheory.EvenCub
end
