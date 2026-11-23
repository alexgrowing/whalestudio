import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HIsom

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A)
    (hu : u ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A))) :
    G * u * G⁻¹ ∈ UJ s J := by
  have hu' : cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
      * (u : Matrix n n A) = cT s (G : Matrix n n A) * J * (G : Matrix n n A) := hu
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  change cT s (((G * u * G⁻¹ : GL n A)) : Matrix n n A) * J
    * (((G * u * G⁻¹ : GL n A)) : Matrix n n A) = J
  simp only [Units.val_mul]
  calc cT s ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
        * ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A))
      = cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
            * (u : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
          * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
        rw [hu']; simp only [cT_mul, Matrix.mul_assoc]
    _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem conj_inv_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) := by
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  have key : cT s ((G⁻¹ : GL n A) : Matrix n n A)
      * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) = J := by
    calc cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A)
        = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
            * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]
  have := conj_mem_UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) G⁻¹ u
    (by rw [key]; exact hu)
  simpa using this

def conjHomeo {T : Type} [Group T] [TopologicalSpace T] [ContinuousMul T] (H' H : Subgroup T) (G : T)
    (h₁ : ∀ u ∈ H', G * u * G⁻¹ ∈ H) (h₂ : ∀ u ∈ H, G⁻¹ * u * G ∈ H') : H' ≃ₜ* H where
  toFun u := ⟨G * u * G⁻¹, h₁ u u.2⟩
  invFun u := ⟨G⁻¹ * u * G, h₂ u u.2⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end Generic

section Base

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem cT_inclR (σ : E →ₐ[F] E) {M : ℕ} (g : Matrix (Fin M) (Fin M) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext i j
  simp [cT, sigR, inclR, Matrix.map_apply]

theorem JR_conj (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) :
    JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) =
      cT (sigR R σ) ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))
        * JR R J * ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  have hG : ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR R) := rfl
  rw [hG, cT_inclR]
  simp only [JR, Matrix.map_mul]

end Base

theorem isTopologicalRing_tens (F E : Type) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.HIsom

open GlobalTheory.CompanionTheory.SW.HIsom in

theorem GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R], ∃ e : HA R σ J' ≃ₜ* HA R σ J, (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J' u * (bc (inclR R) g)⁻¹) ∧ ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J' u ∈ HFin R σ J' := by
  intro F E _ _ _ _ _ σ hCM M J _ g J' hJ' R _ _ _ _
  subst hJ'
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hJR := JR_conj R σ J g
  have h₁ : ∀ u ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)),
      G * u * G⁻¹ ∈ HR R σ J := by
    intro u hu
    refine conj_mem_UJ (sigR R σ) (JR R J) G u ?_
    have : u ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E))) := hu
    rwa [hJR] at this
  have h₂ : ∀ u ∈ HR R σ J,
      G⁻¹ * u * G ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
    intro u hu
    change G⁻¹ * u * G ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)))
    rw [hJR]
    exact conj_inv_mem_UJ (sigR R σ) (JR R J) G u hu
  refine ⟨conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ _ u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ _ u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ _ u := hwu
    simp only [map_mul, map_inv, this, ← hG]
