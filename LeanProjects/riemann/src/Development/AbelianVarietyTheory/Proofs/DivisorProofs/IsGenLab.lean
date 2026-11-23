import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ZH

namespace GlobalTheory.UPoinc.USum

def IsTwVal {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A}
    (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀)
    (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T), α.IsGen ∧ SymLift P.A P.L N N x U ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      gs r z ⊤ v * (val α (r ≫ (ptSecT P.A h).left) z J * val τ (r ≫ β.left) z J).val =
        (GlobalTheory.CommPairing.tval U (r ≫ (ptSecT P.A h).left) z J * val α (r ≫ (ptSecT P.A (x * h)).left) z J).val *
          sval (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => 1) θ
            (r ≫ (ptSecT P.A ((x * h) ^ m)).left ≫ (β ▷ P.A).left) z J

def wtChar {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (a : S.Gam) :
    T →+ ZMod S.N where
  toFun t := ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a)
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

abbrev genPt {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : Over (Sp R) := Over.mk (spMap ψ)

def genTo {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : genPt ψ ⟶ baseOver (Sp R) :=
  Over.homMk (spMap ψ) (Category.comp_id _)

def IsGenLab {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω')
    (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)) : Prop :=
  IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ b, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = (x b).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left) ∧
    ∀ k, x (lab k) = genTo _ ≫ ρ.pt k

end GlobalTheory.UPoinc.USum
