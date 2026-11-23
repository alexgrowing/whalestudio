import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cv (σ : E →ₐ[F] E) (v : Pl F) : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ

def Jv (v : Pl F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E) :=
  J.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)

def liftE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E :=
  TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id

instance isModTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def IsCompIso (σ : E →ₐ[F] E) {m : ℕ} (Y : Spc F E m) (v : Pl F)
    (e : UAtGrp σ Y (evFin F v) ≃* UG (cv σ v) (Jv v Y.J)) : Prop :=
  (∀ g, (((e g : UG (cv σ v) (Jv v Y.J)) : GL (Fin m) (Fv F v ⊗[F] E)) : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) =
      (mat (g : UA σ Y.J)).map (compFin F E v)) ∧ Continuous e ∧ Continuous e.symm

def IsLocCo (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (co : Darboux (symp (R := Fv F v) (cv σ v) (-1) (Jv v X.J) (Jv v W.J)) (Fin n × Fin d)) : Prop :=
  ∀ x : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E), co.e x = GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))

def IsLocChr (χ : Chr F E) (v : Pl F) (χv : (Fv F v ⊗[F] E)ˣ →* Circle) : Prop :=
  ∀ a : (AE F E)ˣ, At (evFin F v) ((a : AE F E) - 1) →
    χv (Units.map (compFin F E v : AE F E →* Fv F v ⊗[F] E) a) = χ a

end GlobalTheory.HoweNonsplit
