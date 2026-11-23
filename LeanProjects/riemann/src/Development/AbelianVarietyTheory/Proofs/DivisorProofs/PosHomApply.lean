import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv

noncomputable section

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def spanA {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
  {u | ∃ y z, u = Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)}

def spanAd {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
  {u | ∃ y z, u = Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z)}

def posHom {R κ ι κ₁ : Type} [AddCommGroup R] (eq : κ ≃ ι ⊕ κ₁) : (κ → R) × (κ → R) →+ (ι → R) where
  toFun w := fun i => w.1 (eq.symm (Sum.inl i))
  map_zero' := rfl
  map_add' _ _ := rfl

def latPos {n d : ℕ} (X : Spc F E n) (W : Spc F E d)
    {Bf : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F} {ι κ₁ : Type}
    (co : Darboux Bf (Fin n × Fin d)) (eq : Fin n × Fin d ≃ ι ⊕ κ₁) (v : Pl F) : AddSubgroup (ι → Fv F v) :=
  ((latAtV X W v).map (GlobalTheory.LatVac.locCo co v)).map (posHom eq)

theorem mem_latPos {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    {Bf : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F} {ι κ₁ : Type}
    {co : Darboux Bf (Fin n × Fin d)} {eq : Fin n × Fin d ≃ ι ⊕ κ₁} {v : Pl F} {y : ι → Fv F v} :
    y ∈ latPos X W co eq v ↔ ∃ γ ∈ latAtV X W v, ∀ i, evFin F v ((co.e γ).1 (eq.symm (Sum.inl i))) = y i := by
  simp only [latPos, AddSubgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, fun i => rfl⟩
  · rintro ⟨γ, hγ, h⟩
    exact ⟨_, ⟨γ, hγ, rfl⟩, funext h⟩

end GlobalTheory.ThK.AdaptEv.VacuumBlock
