import Mathlib
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

abbrev Tr2 : Type := DualNumber (Tr R l)

def tt : Tr2 R l := TrivSqZeroExt.inl (AdjoinRoot.root _)

def ee : Tr2 R l := DualNumber.eps

def inc (k : Type) [CommRing k] [Algebra k R] : R →ₐ[k] Tr2 R l := IsScalarTower.toAlgHom k R (Tr2 R l)

def incD (k : Type) [CommRing k] [Algebra k R] : R →ₐ[k] DualNumber R := IsScalarTower.toAlgHom k R (DualNumber R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

def dlog (κ : Tr2 R l) : R := cf (l - 1) (κ.snd * Ring.inverse κ.fst)

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

theorem algOverHom_comp {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (f : A →ₐ[k] B) (h : B →ₐ[k] C) : algOverHom h ≫ algOverHom f = algOverHom (h.comp f) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp]; rfl

theorem algOverHom_id (A : Type) [CommRing A] [Algebra k A] : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

def Cv (B : Over (Sp k)) : Type 1 := ∀ (S : Type) [CommRing S] [Algebra k S], S → (algOver k S ⟶ B)

variable {B : Over (Sp k)}

def IsAdd [GrpObj B] (cu : Cv B) (l : ℕ) : Prop :=
  (∀ (S S' : Type) [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S'] (ρ : S →ₐ[k] S') (s : S), s ^ l = 0 →
    algOverHom ρ ≫ cu S s = cu S' (ρ s)) ∧
  (∀ (S : Type) [CommRing S] [Algebra k S], cu S 0 = 1) ∧
  ∀ (S : Type) [CommRing S] [Algebra k S] (s s' : S), s ^ l = 0 → s' ^ l = 0 → cu S (s + s') = cu S s * cu S s'

def Along {g : ℕ} (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B) (cv : Fin g → PowerSeries k) (cu : Cv B)
    (l : ℕ) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra k S] (s : S), s ^ l = 0 → ∀ (m : ℕ) (ψ : JetR k (Fin 1 × Fin g) m →ₐ[k] S),
    (∀ j, ψ (zR m ((0 : Fin 1), j)) = Polynomial.aeval s (PowerSeries.trunc l (cv j))) → cu S s = algOverHom ψ ≫ x m

def idx {J : Type} (i j : J) : thK → J := fun I => if (2 : Fin 3) ∈ I.down then j else i

variable {R : Type} [CommRing R] [Algebra k R]

def trip (cu : Cv B) (l : ℕ) (y : algOver k R ⟶ B) : algOver k (Tr2 R l) ⟶ G3 B :=
  lift (cu _ (tt R l)) (lift (cu _ (ee R l)) (algOverHom (inc R l k) ≫ y))

def kap [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L) (cu : Cv B) (l : ℕ) (i j : L.L.ι)
    (y : algOver k R ⟶ B) : Tr2 R l :=
  valR (trip cu l y).left ((Theta B L.L).U (idx i j)) (c.t.s (idx i j)).val

def nu [GrpObj B] (cu : Cv B) (y : algOver k R ⟶ B) (U : B.left.Opens) (a : Γ(B.left, U)) : R :=
  (valR (A := DualNumber R) (cu (DualNumber R) DualNumber.eps * (algOverHom (incD R k) ≫ y)).left U a).snd *
    Ring.inverse (valR y.left U a)

end Points

end GlobalTheory.AddCurve
