import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvAt0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colEq {d d₁ : ℕ} (h : d = d₁ + 2) : Fin d ≃ Fin d₁ ⊕ Fin 2 := (finCongr h).trans finSumFinEquiv.symm

def idx {n d d₁ : ℕ} (h : d = d₁ + 2) : Fin n × Fin d ≃ (Fin n × Fin d₁) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (colEq h)).trans (Equiv.prodSumDistrib _ _ _)

def basM {d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) : Matrix (Fin d) (Fin d) E :=
  fun r c => Sum.elim (fun j => H'.ι r j) (fun k : Fin 2 => if k = 0 then H'.x r else H'.y r) (colEq h c)

def dec {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) where
  toFun w := w * (incM F (basM h H')⁻¹)ᵀ
  map_add' w w' := Matrix.add_mul _ _ _
  map_smul' c w := Matrix.smul_mul _ _ _

def zPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d₁) (AE F E) where
  toFun w i j := dec h H' w i ((colEq h).symm (Sum.inl j))
  map_add' w w' := by ext i j; simp only [map_add]; rfl
  map_smul' c w := by ext i j; simp only [map_smul]; rfl

def aPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n → AE F E) where
  toFun w i := dec h H' w i ((colEq h).symm (Sum.inr 0))
  map_add' w w' := by ext i; simp only [map_add]; rfl
  map_smul' c w := by ext i; simp only [map_smul]; rfl

def bPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n → AE F E) where
  toFun w i := dec h H' w i ((colEq h).symm (Sum.inr 1))
  map_add' w w' := by ext i; simp only [map_add]; rfl
  map_smul' c w := by ext i; simp only [map_smul]; rfl

variable (F E) in

def tb (h2 : Module.finrank F E = 2) : Module.Basis (Fin 2) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasisOfFinrankEq F E h2)

def tCo (h2 : Module.finrank F E = 2) {n : ℕ} : (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin 2 → AF F) where
  toFun b p := (tb F E h2).repr (b p.1) p.2
  map_add' b b' := by ext p; simp
  map_smul' c b := by ext p; simp

def mCo (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) {n : ℕ} (X : Spc F E n) :
    (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin 2 → AF F) where
  toFun a p := Algebra.trace (AF F) (AE F E) (tb F E h2 p.2 * (incM F X.J *ᵥ fun k => cA σ (a k)) p.1)
  map_add' a a' := by
    ext p
    have e : (fun k => cA σ (a k + a' k)) = (fun k => cA σ (a k)) + fun k => cA σ (a' k) := by
      ext k; simp
    simp only [Pi.add_apply]
    rw [e, Matrix.mulVec_add, Pi.add_apply, mul_add, map_add]
  map_smul' c a := by
    ext p
    have e : (fun k => cA σ (c • a k)) = c • fun k => cA σ (a k) := by
      ext k; simp
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, mul_smul_comm, map_smul]

def glue {n d d₁ : ℕ} (h : d = d₁ + 2) {R : Type} (p : Fin n × Fin d₁ → R) (q : Fin n × Fin 2 → R) : Fin n × Fin d → R :=
  fun k => Sum.elim p q (idx h k)

theorem glue_inl {n d d₁ : ℕ} (h : d = d₁ + 2) {R : Type} (p : Fin n × Fin d₁ → R) (q : Fin n × Fin 2 → R)
    (j : Fin n × Fin d₁) : glue h p q ((idx h).symm (Sum.inl j)) = p j := by
  simp [glue]

variable (σ : E →ₐ[F] E) {n d d₁ : ℕ} (h2 : Module.finrank F E = 2) (X : Spc F E n) (W : Spc F E d) {W₁ : Spc F E d₁}
  (h : d = d₁ + 2) (H' : Plane E d d₁) (M₁ : Model σ X W₁)

def coL : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) where
  toFun w := (glue h (M₁.co.e (zPart h H' w)).1 (tCo h2 (bPart h H' w)),
    glue h (M₁.co.e (zPart h H' w)).2 (mCo σ h2 X (aPart h H' w)))
  map_add' w w' := by
    ext k <;> simp only [glue, map_add, Prod.fst_add, Prod.snd_add, Prod.fst_add, Pi.add_apply] <;>
      cases idx h k <;> simp
  map_smul' c w := by
    ext k <;> simp only [glue, map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply] <;>
      cases idx h k <;> simp

def coA (hb : Function.Bijective (coL σ h2 X h H' M₁))
    (hf : ∀ w w', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (coL σ h2 X h H' M₁ w).1 ⬝ᵥ (coL σ h2 X h H' M₁ w').2 - (coL σ h2 X h H' M₁ w').1 ⬝ᵥ (coL σ h2 X h H' M₁ w).2) :
    Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
  ⟨LinearEquiv.ofBijective (coL σ h2 X h H' M₁) hb, hf⟩

def latPl (v : Pl F) : Set (Fin n × Fin 2 → Fv F v) :=
  {t | ∃ γ ∈ latAtV X W v, zPart h H' γ = 0 ∧ aPart h H' γ = 0 ∧ t = fun p => evFin F v (tCo h2 (bPart h H' γ) p)}

def vacA (v : Pl F) (x : Fin n × Fin d → Fv F v) : ℂ :=
  Set.indicator (latPl h2 X W h H' v) 1 (fun p => x ((idx h).symm (Sum.inr p))) *
    M₁.vac v (fun q => x ((idx h).symm (Sum.inl q)))

def Ma (M : Model σ X W) (hb : Function.Bijective (coL σ h2 X h H' M₁))
    (hf : ∀ w w', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (coL σ h2 X h H' M₁ w).1 ⬝ᵥ (coL σ h2 X h H' M₁ w').2 - (coL σ h2 X h H' M₁ w').1 ⬝ᵥ (coL σ h2 X h H' M₁ w).2) :
    Model σ X W :=
  ⟨coA σ h2 X W h H' M₁ hb hf, vacA σ h2 X W h H' M₁, M.μ, M.dom⟩

omit σ h2 X W H' M₁

def eA : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ fun y => glue h y 0

def evA (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ fun y => glue h y 0

open scoped Classical in

def incInf : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => glue h y 0
      map_add' := fun y y' => by funext k; simp only [glue, Pi.add_apply]; cases idx h k <;> simp
      map_smul' := fun c y => by funext k; simp only [glue, Pi.smul_apply, RingHom.id_apply]; cases idx h k <;> simp }

open scoped Classical in
theorem norm_le_incInf (y : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖y‖ ≤ ‖incInf h y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have e : y j = incInf h y ((idx h).symm (Sum.inl j)) := (glue_inl h y 0 j).symm
  rw [e]
  exact norm_le_pi_norm (incInf h y) _

open scoped Classical in

def eiA : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (incInf (F := F) h).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_incInf (F := F) h y
      have h0 := norm_nonneg (incInf (F := F) h y)
      simp only [pow_one, one_mul]
      linarith⟩

end GlobalTheory.ThK.EvAt0
