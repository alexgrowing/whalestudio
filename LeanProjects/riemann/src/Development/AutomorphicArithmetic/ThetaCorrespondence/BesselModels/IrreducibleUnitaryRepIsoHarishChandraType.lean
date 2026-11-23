import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HWSpan
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.KShift

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType

theorem exists_hcType_of_irred : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  intro k Wp _ _ _ _ ρ hρ hirr
  obtain ⟨E, hgl, hun, hE⟩ := Derived.exists_derived_action k Wp ρ hρ
  have hQ : CompanionTheory.D.DSIC.KStab (PI.UpqRep.allPos k) E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ _ => trivial
  obtain ⟨μ, x, -, hx0, hx⟩ := UpperTheory.Lit.Bur.KShift.exists_highest hgl (UpperTheory.Lit.Bur.KShift.kUnit_of hun) hQ top_ne_bot
  have hlow : PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k) = μ := by
    rw [GlobalTheory.KTypeCompare.lowK_allPos]
    simp
  have hΛ : Formalism.REAL.KHighest (PI.UpqRep.allPos k) E
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k)) x := by
    rw [hlow]; exact hx
  have htype := exists_type_of_highest hρ E hgl hun hE _ x hx0 hΛ
  set S := Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x with hS
  have hst := Wt.stable_of_derived hρ E hE S (Formalism.REAL.isCompactInvariant_compactSpan x)
  have hxS : x ∈ S := Formalism.REAL.mem_compactSpan x
  have htop : S = ⊤ := (hirr S hst).resolve_left fun h => hx0 (by
    rw [h] at hxS; exact (Submodule.mem_bot ℂ).1 hxS)
  refine ⟨_, S, inferInstance, inferInstance, compress ρ S, (LinearEquiv.ofTop S htop).symm, htype, ?_⟩
  intro h hh w
  apply Subtype.ext
  rw [coe_compress (hst h hh _ (Subtype.property _))]
  simp [LinearEquiv.ofTop_symm_apply]

end UpperTheory.Lit.Bur.HWSpanType

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  first | exact @UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | exact UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | (intros; apply UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred <;> assumption)
