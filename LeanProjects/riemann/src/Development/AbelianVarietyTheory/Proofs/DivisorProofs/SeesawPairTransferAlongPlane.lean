import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDescendsAlongAdaptedPlane

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrXDbl

open GlobalTheory.MixedLagrX

def dblRat (F : Type) [Field F] (κ : Type) :
    ((κ → F) × (κ → F)) × ((κ → F) × (κ → F)) →ₗ[F] (κ ⊕ κ → F) × (κ ⊕ κ → F) where
  toFun u := (Sum.elim u.1.1 u.2.1, Sum.elim u.1.2 (-u.2.2))
  map_add' u v := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp [add_comm]
  map_smul' c u := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp

theorem dblRat_injective (F : Type) [Field F] (κ : Type) : Function.Injective (dblRat F κ) := by
  intro u v h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [dblRat, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext i; exact congrFun h1 (Sum.inl i)
  · funext i; exact congrFun h2 (Sum.inl i)
  · funext i; exact congrFun h1 (Sum.inr i)
  · funext i; simpa using congrFun h2 (Sum.inr i)

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∃ L : Submodule F ((Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d ⊕ Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ y : Fin d ⊕ Fin d → AE F E, ∃ z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E),
          (dd₁.e z).1 = 0 ∧ dd.e (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * z) =
            t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁
  obtain ⟨L₀, hiso, hrank, hadel⟩ := GlobalTheory.MixedLagrX.exists_ratLagr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁
    M₁ om₁ r₁ s₁ hH hP₁
  let T := dblRat F (Fin n × Fin d) ∘ₗ (L₀.subtype.prodMap L₀.subtype)
  have hT : ∀ p q : L₀, T (p, q) = (Sum.elim p.1.1 q.1.1, Sum.elim p.1.2 (-q.1.2)) :=
    fun _ _ => rfl
  have hTinj : Function.Injective T := by
    refine (dblRat_injective F _).comp ?_
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [LinearMap.prodMap_apply, Submodule.subtype_apply, Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  refine ⟨LinearMap.range T, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨p, q⟩, rfl⟩ _ ⟨⟨p', q'⟩, rfl⟩
    rw [hT, hT]
    simp only [sumElim_dotProduct_sumElim, dotProduct_neg]
    rw [hiso _ p.2 _ p'.2, hiso _ q.2 _ q'.2]
  · rw [LinearMap.finrank_range_of_inj hTinj, Module.finrank_prod, hrank]
    simp [Fintype.card_sum]
  · rintro t _ ⟨⟨p, q⟩, rfl⟩
    obtain ⟨a, z, hz, he⟩ := hadel t p p.2
    obtain ⟨a', z', hz', he'⟩ := hadel t q q.2
    refine ⟨Sum.elim a a', Matrix.fromCols z z', ?_, ?_⟩
    · rw [hdd₁, hz, hz']
      exact Sum.elim_zero_zero
    · have hsplit : Matrix.vecMulVec (incV F H.x) (Sum.elim a a') + incM F H.ι * Matrix.fromCols z z' =
          Matrix.fromCols (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z)
            (Matrix.vecMulVec (incV F H.x) a' + incM F H.ι * z') := by
        ext i (j | j) <;> simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
      rw [hsplit, hdd, he, he', hT]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp

end GlobalTheory.MixedLagrXDbl

end
