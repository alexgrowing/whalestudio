import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
open Matrix

namespace GlobalTheory.PMon

theorem matrixHomRepresentationCocycleCoords_cocycle {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {G : Type*} [Group G] (ρ : G →* GL (a ⊕ b) R) (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (c : G → Matrix a b R)
    (hρ : ∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (ρ₁ g : Matrix a a R) (c g) 0 (ρ₂ g : Matrix b b R))
    (g h : G) :
    extCoc ρ₂ c (g * h) = extCoc ρ₂ c g + ((homRep ρ₁ ρ₂ g : GL (a × b) R) : Matrix (a × b) (a × b) R).mulVec (extCoc ρ₂ c h) := by
  have hc : c (g * h) = (ρ₁ g : Matrix a a R) * c h + c g * (ρ₂ h : Matrix b b R) := by
    have := congrArg (fun M : GL (a ⊕ b) R => Matrix.toBlocks₁₂ (M : Matrix (a ⊕ b) (a ⊕ b) R)) (map_mul ρ g h)
    simp only [Units.val_mul, hρ, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at this
    simpa using this
  unfold extCoc
  rw [homRep_apply, homUnit_val, kronecker_transpose_mulVec]
  rw [hc, map_mul, _root_.mul_inv_rev, Units.val_mul]
  have h2 : (ρ₂ h : Matrix b b R) * (((ρ₂ h)⁻¹ : GL b R) : Matrix b b R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.add_mul, Matrix.mul_assoc (c g), ← Matrix.mul_assoc (ρ₂ h : Matrix b b R), h2, Matrix.one_mul]
  funext p
  simp only [vecM, Pi.add_apply, Matrix.add_apply, Matrix.mul_assoc]
  ring

theorem extCoc_rat_cont_cocycle : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hrat hρ
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have hent : ∀ g (i : a) (k : b), c g i k = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inr k) := by
    intro g i k; rw [hρ]; rfl
  have hinv : ∀ g (k j : b), (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)) k j =
      (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr j) := by
    intro g k j; rw [← map_inv, hρ]; rfl
  have hform : ∀ g (i : a × b), extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i =
      ∑ k, (ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) *
        (ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) := by
    intro g i
    simp only [extCoc, vecM, MonoidHom.comp_apply, Matrix.mul_apply, hent, hinv]
  have hcι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  refine ⟨?_, ?_, ?_⟩
  · intro g i
    rw [hform, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hrat.rat, hrat.rat]
  · intro i
    have : (fun g => ((extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, (((ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) : ↥(MaximalUnramifiedExtension l)) : Om l) *
          (((ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [hform]
      push_cast
      rfl
    rw [this]
    refine continuous_finset_sum _ fun k _ => ?_
    exact ((hrat.cont _ _).comp hcι).mul ((hrat.cont _ _).comp (continuous_inv.comp hcι))
  · intro g h
    exact matrixHomRepresentationCocycleCoords_cocycle (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hρ (ι g)) g h

end GlobalTheory.PMon
