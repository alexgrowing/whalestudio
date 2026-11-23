import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorDeterminantPairEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnEquivStatement

namespace GlobalTheory.IndLineGL
open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

section General
variable {G H V Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem HomLeOne.of_comp {ρ : Representation ℂ G V} {τ : Representation ℂ G Y} (φ : H →* G)
    (h : HomLeOne (ρ.comp φ) (τ.comp φ)) : HomLeOne ρ τ := by
  intro μ μ'
  exact h ⟨μ.toLinearMap, fun x => μ.isIntertwining' (φ x)⟩ ⟨μ'.toLinearMap, fun x => μ'.isIntertwining' (φ x)⟩

theorem homLeOne_of_scalar {ρ : Representation ℂ G V} {τ : Representation ℂ G Y} (hρ : ρ.IsIrreducible)
    (hτ : τ.IsIrreducible) (hs : ∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) : HomLeOne ρ τ := by
  intro μ μ'
  rcases Representation.IsIrreducible.bijective_or_eq_zero μ with hb | h0
  · right
    let e := μ.ofBijective hb
    obtain ⟨c, hc⟩ := hs (e.symm.toIntertwiningMap.comp μ')
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    have h1 : μ (e.symm (μ' v)) = μ' v := e.apply_symm_apply (μ' v)
    have h2 : e.symm (μ' v) = c • v := hc v
    rw [h2, map_smul] at h1
    exact h1.symm
  · left
    rw [h0]; rfl

def equivComp {ρ : Representation ℂ G V} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) (φ : H →* G) :
    Representation.Equiv (ρ.comp φ) (τ.comp φ) :=
  .mk e.toLinearEquiv fun x => by
    exact e.toIntertwiningMap.isIntertwining' (φ x)

end General
end GlobalTheory.IndLineGL

namespace GlobalTheory.IndLineGL
open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tgt_comp_midIncl {m : ℕ} {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁)
    (ξ₁ ξ₂ : kˣ →* ℂˣ) :
    (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹).comp (midIncl k m) = σ₁ := by
  ext h y
  have h0 : (midIncl k m h) 0 = 1 := by
    show Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h 0 = 1
    exact Pi.mulSingle_eq_of_ne (by decide) _
  have h2 : (midIncl k m h) 2 = 1 := by
    show Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h 2 = 1
    exact Pi.mulSingle_eq_of_ne (by decide) _
  have h1 : (midIncl k m h) 1 = h := by
    show Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h 1 = h
    exact Pi.mulSingle_eq_same _ _
  have hd : deltaHalf k (fun i : Fin 3 => Fin (blk3 m i)) (midIncl k m h) = 1 := by
    rw [deltaHalf_apply, Fin.prod_univ_three, h0, h2, h1]
    have hm : modExp (fun i : Fin 3 => Fin (blk3 m i)) 1 = 0 := by
      simp [modExp, Finset.sum_filter, Fin.sum_univ_three]
    rw [hm, map_one, map_one, map_one, map_one, mul_one]
    simp
  show (((deltaHalf k _ (midIncl k m h))⁻¹ : ℂˣ) : ℂ) • leviTgt σ₁ ξ₁ ξ₂ (midIncl k m h) y = σ₁ h y
  rw [hd, leviTgt_apply, h0, h2, h1, map_one, map_one, map_one, map_one, mul_one]
  simp

theorem isIrreducible_comp_glCast {n m : ℕ} (h : n = m) {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁]
    (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (hσ : σ₁.IsIrreducible) :
    Representation.IsIrreducible (σ₁.comp (glCast k h)) := by
  subst h
  rw [glCast_rfl]
  exact hσ

theorem homLeOne_cellFunctor_leviTgt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.ThK.KP → ∀ (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁), σ₁.IsIrreducible →
    ∀ (ξ₁ ξ₂ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
      (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j)),
      (cellMid k α₀ β₀ b.1).IsIrreducible →
      HomLeOne (cellFunctor f g (detPair k a a' α₀ β₀))
        (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹) := by
  intro k _ _ _ _ _ a a' m α₀ β₀ hα hβ P₁ _ _ σ₁ hσ ξ₁ ξ₂ b f g hmid
  have hm : b.1 false 1 + b.1 true 1 = m := by
    have := b.2.2 1
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    change b.1 true 1 + b.1 false 1 = m at this
    omega
  have e1 := (GlobalTheory.T.cell_functor_determinant_pair_equiv k a a' m α₀ β₀ hα hβ b f g).some
  have e2 := (GlobalTheory.T.parabolic_induction_column_equiv k a a' m α₀ β₀ b f g hm).some
  have e : Representation.Equiv ((cellFunctor f g (detPair k a a' α₀ β₀)).comp ((midIncl k m).comp (glCast k hm)))
      (cellMid k α₀ β₀ b.1) := (equivComp e1 (glCast k hm)).trans e2
  refine HomLeOne.of_comp ((midIncl k m).comp (glCast k hm)) (HomLeOne.of_equiv e ?_)
  have ht : (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹).comp
      ((midIncl k m).comp (glCast k hm)) = σ₁.comp (glCast k hm) := by
    rw [← MonoidHom.comp_assoc, tgt_comp_midIncl]
  rw [ht]
  exact homLeOne_of_scalar hmid (isIrreducible_comp_glCast hm σ₁ hσ)
    (GlobalTheory.LocGL.schur_GL (isSmooth_prod₂ _ _) hmid)

end GlobalTheory.IndLineGL
