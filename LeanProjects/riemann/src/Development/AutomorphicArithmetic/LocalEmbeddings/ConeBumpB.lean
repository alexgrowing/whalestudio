import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact

noncomputable section

namespace GlobalTheory.ConeBumpB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.VanishLoc (liftT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Points

variable {n n₁ d d₁ : ℕ}

def uS (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (s : Fv F v ⊗[F] E) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  cA σ (liftT v s) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)

def yAt (H' : Plane E d d₁) (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.vecMulVec (fun i => liftT v (y i)) (incV F H'.x)

def atV (v : Pl F) (x : Fin n → AE F E) : Fin n → Fv F v ⊗[F] E := fun i => compFin F E v (x i)

def pairV (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y : Fin n → Fv F v ⊗[F] E) : Fv F v ⊗[F] E :=
  x ⬝ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ fun i => sigR (Fv F v) σ (y i))

def dispA {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E) (k : UA σ J) (t : Fv F v ⊗[F] E) :
    Fin n → Fv F v ⊗[F] E :=
  t • atV v (mat k⁻¹ *ᵥ incV F x₀) - atV v (incV F x₀)

theorem disp_eq {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E) (k : UA σ J) (l : (AE F E)ˣ) :
    GlobalTheory.ConeBump.disp v x₀ k l = dispA v x₀ k (compFin F E v l.1) := by
  funext i
  simp only [GlobalTheory.ConeBump.disp, dispA, atV, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem partFin_liftT (v : Pl F) (z : AE F E) : partFin v (liftT v (compFin F E v z)) = partFin v z := by
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
  · rw [partFin, partFin, compInf_smul, compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v 1) = 0 from rfl, zero_smul,
      zero_smul]
  · rw [partFin, partFin, compFin_smul, compFin_smul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.LocPair.compFin_liftT]
    · rw [show evFin F w (GlobalTheory.LatVac.liftV v 1) = 0 from evalV_singleFin_ne hw 1, zero_smul, zero_smul]

theorem partFin_shiftB (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (l : (AE F E)ˣ) :
    partFin v (shiftB σ H H' l) = partFin v (uS σ H H' v (compFin F E v l.1)) := by
  have h := partFin_liftT v l.1
  rw [partFin, partFin] at h
  rw [partFin, partFin, smul_shiftB, ← h, uS, map_smul]
  exact smul_assoc _ _ _

theorem uS_zero (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) : uS σ H H' v 0 = 0 := by
  rw [uS, map_zero, map_zero, zero_smul]

theorem pairV_add_right (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y y' : Fin n → Fv F v ⊗[F] E) :
    pairV σ J v x (y + y') = pairV σ J v x y + pairV σ J v x y' := by
  have e : (fun i => sigR (Fv F v) σ ((y + y') i)) =
      (fun i => sigR (Fv F v) σ (y i)) + fun i => sigR (Fv F v) σ (y' i) := funext fun i => map_add _ _ _
  rw [pairV, pairV, pairV, e, Matrix.mulVec_add, dotProduct_add]

theorem pairV_smul_sub_left (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (t : Fv F v ⊗[F] E)
    (x x' y : Fin n → Fv F v ⊗[F] E) : pairV σ J v (t • x - x') y = t * pairV σ J v x y - pairV σ J v x' y := by
  rw [pairV, pairV, pairV, sub_dotProduct, smul_dotProduct, smul_eq_mul]

end Points

def evS {σ : E →ₐ[F] E} {n d n₁ d₁ m m' : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (v : Pl F)
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (H : Plane E n m) (H' : Plane E d m')
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (s : Fv F v ⊗[F] E) : (Fin n₁ × Fin d₁ → Fv F v) → ℂ :=
  ev (locOp v (M.co.rho B.ψ (partFin v (uS σ H H' v s))) φ)

def four (v : Pl F) (ψ : AddChar (Fv F v) ℂ) [MeasurableSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E))
    (T : Fv F v ⊗[F] E → ℂ) (t : Fv F v ⊗[F] E) : ℂ :=
  ∫ s, T s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) ∂m

end GlobalTheory.ConeBumpB

end
