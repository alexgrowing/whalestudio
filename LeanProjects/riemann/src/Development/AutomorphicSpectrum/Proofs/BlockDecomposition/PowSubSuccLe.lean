import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FinitenessStep
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}

def secs {E : X.Modules} (S : Subobject E) (V : X.Opens) : Set Γ(E, V) :=
  Set.range (S.arrow.app V)

def Killed (J : X.IdealSheafData) {E : X.Modules} (S : Subobject E) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x : Γ(E, U), a • x ∈ secs S U

variable [X.Over (Spec (.of A))]

def powSub (E : X.Modules) (n : ℕ) : Subobject E := Subobject.mk (idealPowι I E n)

def PropSupp (A : Type) [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules}
    (S : Subobject E) : Prop :=
  ∃ T : X.IdealSheafData, IsProper (T.subschemeι ≫ (X ↘ Spec (.of A))) ∧
    Scheme.Modules.SupportedIn (cokernel S.arrow) (T.support : Set X)

structure ClosedSys (E : X.Modules) (S : ℕ → Subobject E) : Prop where
  qcoh : ∀ e, (S e : X.Modules).IsQuasicoherent
  pow_le : ∀ e, powSub I E (e + 1) ≤ S e
  succ : ∀ e, S e = S (e + 1) ⊔ powSub I E (e + 1)

def Alg (E : X.Modules) (S : ℕ → Subobject E) : Prop :=
  ∃ B : Subobject E, (B : X.Modules).IsQuasicoherent ∧ PropSupp A B ∧
    ∀ e, B ⊔ powSub I E (e + 1) = S e

def Statement (J : X.IdealSheafData) : Prop :=
  ∀ (E : X.Modules), IsCoherent E → ∀ S : ℕ → Subobject E, ClosedSys I E S →
    (∀ e, Killed J (S e)) → PropSupp A (S 0) → Alg I E S

def restrictSys {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (c e : ℕ) :
    Subobject (D : X.Modules) :=
  (Subobject.pullback D.arrow).obj (S (e + c)) ⊔ powSub I (D : X.Modules) (e + 1)

lemma powSub_succ_le (E : X.Modules) (n : ℕ) : powSub I E (n + 1) ≤ powSub I E n :=
  Subobject.mk_le_mk_of_comm (idealPowSucc I E n) (idealPowSucc_ι I E n)

theorem closedSys_pow (E : X.Modules) [E.IsQuasicoherent] :
    ClosedSys I E (fun e => powSub I E (e + 1)) where
  qcoh e := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealPowι I E (e + 1))).symm inferInstance
  pow_le _ := le_rfl
  succ e := (sup_eq_right.2 (powSub_succ_le I E (e + 1))).symm

end GlobalTheory.CompanionTheory.GE
