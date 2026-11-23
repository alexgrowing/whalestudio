import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContainsRayField {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (M : ℕ) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 L), ((M : ℕ) : 𝓞 L) ∉ 𝔓.asIdeal →
    ∃ (f : ℕ) (α : 𝓞 K),
      Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f ∧
      (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f = Ideal.span {α} ∧ ((M : ℕ) : 𝓞 K) ∣ α - 1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Tuple

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable (D) in

def embK : D.host.K →+* D.what₂.LL := D.embE.comp (algebraMap D.host.K D.host.E)

def tupLevel (t : T0) : ℕ :=
  D.host.g 0 * D.host.g 1 * ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

structure FieldHyp (t : T0) : Prop where
  xi : ∀ x, ((R.xi t x : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange
  eta : ∀ P, Formalism.L2.Host.etaAlg D.host R.C.eta P ∈ D.what₂.embLL.fieldRange
  roots : ∀ PP ∈ R.Q t, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  comp : ContainsRayField (embK D) (tupLevel R t)

def RatAt (i : Fin D.R.m) (ph : ℂ) (t : T0) : Prop :=
  ∀ x₀ : A.fam.amb.FL i t, ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t (R.jV i t x₀) ∧
    ph • R.thG i t (R.jV i t x₀) =
      (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)

theorem proj_clause (i : Fin D.R.m) (ph : ℂ) (t : T0) (hG : R.thP_thG)
    (hinj : Function.Injective (R.HW i (sg0 D A)).e)
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi (R.FW i).ρ)
    (x : (R.HV i t).H) (y : Fin (R.nW i) → D.what₂.LL)
    (h : (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t x) :
    ph • R.thG i t x = (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) := by
  apply hinj
  rw [map_smul, hG i t x, ← map_smul, ← h, Arith.FormsL.eOp, LinearMap.sum_apply, map_sum, map_sum]
  have key : ∀ g : G, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A)
      ((((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g) y)) =
      RealDat.eC (A := A) (sg0 D A) g • actW R i _ g ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y)) := by
    intro g
    rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, hρ g y, smul_smul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun g _ => key g]
  generalize (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = Φ
  ext v h
  simp [RealDat.eWf, gaL, actW, postOn, LinearMap.sum_apply, Finset.sum_apply]
  first | rfl | exact Finset.sum_congr rfl fun _ _ => rfl

end Tuple

def RatThetaAt (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → RhoTie R → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → QGuard R →
    ∀ t : T0, FieldHyp R t → RatAt R i (ph i) t

def RatTheta : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m),
    RatThetaAt T R F κ v₀ O ph i

end GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta
