import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSchurLemma

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem UpperTheory.Lit.Cas.schur_adm : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm

private theorem UpperTheory.Lit.Cas.exists_ne_zero_of_irr {G N : Type} [Group G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) (hirr : π.IsIrreducible) : ∃ x : N, x ≠ 0 := by
  have hne : (⊥ : Subrepresentation π) ≠ ⊤ := bot_ne_top
  by_contra h
  push Not at h
  apply hne
  ext v
  simp [h v]

theorem UpperTheory.Lit.Cas.schur :
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (t : kˣ), (∃ c, ScalarBy x t c) ∧ (∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c') ∧ ∀ c, x.1 = 0 → ScalarBy x t c → c = 1 := by
  intro H k _ _ _ _ x t
  obtain ⟨v, hv⟩ := UpperTheory.Lit.Cas.exists_ne_zero_of_irr x.rep x.2.rep.irr
  have uniq : ∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c' := fun c c' h h' =>
    smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  refine ⟨?_, uniq, fun c h0 hc => uniq _ _ hc fun w => ?_⟩
  · obtain ⟨c, hc⟩ := UpperTheory.Lit.Cas.schur_adm (GL (Fin x.1) k) (KO k (Fin x.1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ x.rep x.2.rep.irr (H k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr)
      (x.rep (Matrix.GeneralLinearGroup.scalar (Fin x.1) t)) (fun g w => by
        have hcomm : Matrix.GeneralLinearGroup.scalar (Fin x.1) t * g =
            g * Matrix.GeneralLinearGroup.scalar (Fin x.1) t := by
          apply Units.ext
          exact (Matrix.scalar_commute (n := Fin x.1) (t : k) (fun r => Commute.all _ _) (g : Matrix _ _ k)).eq
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply])
    exact ⟨c, fun w => by rw [hc]; rfl⟩
  · haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin x.1) t = 1 :=
      Units.ext (Matrix.ext fun i => isEmptyElim i)
    rw [h1, map_one, one_smul]; rfl
