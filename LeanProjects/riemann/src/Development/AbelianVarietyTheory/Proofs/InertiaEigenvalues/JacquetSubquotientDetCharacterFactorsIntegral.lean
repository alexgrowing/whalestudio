import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

open GlobalTheory.SmGL.DepthZero ValuativeRel Matrix

theorem factor_eq_det_of_isSubquotient_jac : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  intro F _ _ _ _ n β _ _ _ _ c f V _ _ σ ψ s ⟨E⟩ hsub j g hg v
  classical

  have hσ : ∀ (h : GL n F) (x : V), σ h x = (ψ (GeneralLinearGroup.det h) : ℂ) • x := by
    intro h x
    apply E.toLinearEquiv.injective
    have h1 := E.toIntertwiningMap.isIntertwining σ (detRep n ψ) h x
    have h2 : E.toLinearEquiv (σ h x) = E.toIntertwiningMap (σ h x) := rfl
    have h3 : E.toLinearEquiv x = E.toIntertwiningMap x := rfl
    rw [h2, h1, map_smul, h3]
    simp [detRep]

  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {h : GL d F}, h ∈ KO F d →
      valuation F (GeneralLinearGroup.det h : F) = 1 := by
    intro d _ _ h hh
    obtain ⟨h, rfl⟩ := hh
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) h) : Fˣ) : F) =
        algebraMap 𝒪[F] F (GeneralLinearGroup.det h : 𝒪[F]ˣ) :=
      ((algebraMap 𝒪[F] F).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation F)).one_of_isUnit (Units.isUnit _)
  set l : Levi F (fun j => Fin (c j)) := Pi.mulSingle j g with hl
  have hlK : ∀ b, l b ∈ KO F (Fin (c b)) := by
    intro b
    by_cases hb : b = j
    · subst hb; simp [l, hg]
    · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
  have hdet : GeneralLinearGroup.det (leviEmb F f l) = GeneralLinearGroup.det g := by
    rw [det_leviEmb, Finset.prod_eq_single j]
    · simp [l]
    · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
    · simp
  have hδ : deltaHalf F (fun j => Fin (c j)) l = 1 := by
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ (hval (hlK b))

  have hjac : ∀ x, jac f σ l x = (ψ (GeneralLinearGroup.det g) : ℂ) • x := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [jac_mk, hδ, inv_one, Units.val_one, one_smul, hσ, hdet, Submodule.Quotient.mk_smul]

  have hT := Model.scalar_of_isSubquotient hsub hjac

  have hnt : ∀ b, Nontrivial (s b).V := fun b => Model.nontrivial_of_isIrreducible (s b).irr
  have hφ : ∀ b, ∃ x : (s b).V, ∃ φ : (s b).V →ₗ[ℂ] ℂ, φ x ≠ 0 := by
    intro b
    obtain ⟨x, hx⟩ := exists_ne (0 : (s b).V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (s b).V, φ x ≠ 0 := by
      by_contra! h
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)
    exact ⟨x, φ, hφ⟩
  choose x φ hxφ using hφ
  let y : ∀ b, (s b).V := Function.update x j v
  have hc : (∏ b ∈ Finset.univ.erase j, φ b (y b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    rw [show y b = x b from Function.update_of_ne (Finset.ne_of_mem_erase hb) _ _]
    exact hxφ b
  have hyj : y j = v := Function.update_self _ _ _
  have key := contract_piTensor (fun b => (s b).ρ) φ j g (PiTensorProduct.tprod ℂ y)
  rw [hT, map_smul, contract_tprod, hyj, map_smul] at key
  rw [smul_comm] at key
  exact (smul_right_injective _ hc key).symm

end GlobalTheory.LevelType
