import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTauEmbPosPlConjEq

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem eTau_tauSg (D : D7) (τ : D.what₂.Tau) :
    ((D.eTau (tauSg D τ) : D.R.Psi) : D.R.GG) =
      (D.eTau τ : D.R.GG) * sgm D := by
  have h : (D.eTau τ : D.R.GG) * sgm D ∈ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]
    have := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    simp [sgm, this]
  unfold tauSg
  rw [dif_pos h, Equiv.apply_symm_apply]

theorem sgm_mul_sgm (D : D7) : sgm D * sgm D = 1 := by
  simp [sgm, Prod.ext_iff]

theorem sgm_ne_one (D : D7) : sgm D ≠ 1 := by
  intro h
  have : (((sgm D).1.1 : ℤˣ) : ℤ) = 1 := by rw [h]; rfl
  simp [sgm] at this

theorem sgm_mul_cc (D : D7) : sgm D * D.R.cc = ((1, -1), 1) := by
  simp [sgm, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem tauSg_invol_norm_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.d →
    ∀ (τ : D.what₂.Tau), tauSg D (tauSg D τ) = τ ∧ tauSg D τ ≠ τ ∧
      ∀ y : D.host.E, ‖tauEmb D lam (tauSg D τ) (D.host.conj y)‖ = ‖tauEmb D lam τ y‖ := by
  intro D p _ lam hp τ
  subst hp
  refine ⟨?_, ?_, ?_⟩
  · apply D.eTau.injective
    apply Subtype.ext
    rw [eTau_tauSg, eTau_tauSg, mul_assoc, sgm_mul_sgm, mul_one]
  · intro h
    have h1 := congrArg (fun t => ((D.eTau t : D.R.Psi) : D.R.GG)) h
    simp only [eTau_tauSg] at h1
    exact sgm_ne_one D (mul_eq_left.mp h1)
  · intro y
    set g : D.R.GG := (D.eTau τ : D.R.GG) with hg
    let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf ((1, -1), 1)
    have hgσ : D.host.galE σ = ((1, -1), 1) := by
      change D.host.galE
        ((D.host.gal).symm ((1, -1), 1)) = _
      exact D.host.gal.apply_symm_apply _
    have hemb : embT D (tauSg D τ) (D.host.conj y) = embT D τ (σ y) := by
      change D.host.emb _ (D.host.conj y) = D.host.emb g (σ y)
      rw [eTau_tauSg, ← hg]
      have e1 := emb_mul_galE D.host (g * sgm D) D.host.conj y
      have e2 := emb_mul_galE D.host g σ y
      have hc : D.host.galE D.host.conj = D.R.cc :=
        D.host.galE_conjE
      rw [hc] at e1
      rw [hgσ] at e2
      rw [← e1, ← e2, mul_assoc, sgm_mul_cc]
    have hsp : SamePrime (rhoH D lam τ) ((rhoH D lam τ).comp (σ : D.host.E →+* D.host.E)) := by
      intro a
      have hPp := primeOf_isPrime (rhoH D lam τ)
      have hd : (D.host.d : 𝓞 D.host.E) ∈ primeOf (rhoH D lam τ) := natCast_mem_primeOf _
      obtain ⟨z, hz, hze⟩ := (Formalism.MainNotions.GlobalTheoryTheory.jnt_inertiaD D _ hPp hd σ).2 (Or.inr hgσ) a
      have hz' : ‖rhoH D lam τ (σ (a : D.host.E)) - rhoH D lam τ (a : D.host.E)‖ < 1 := by
        rw [← map_sub, ← hze]
        exact hz
      change ‖rhoH D lam τ (a : D.host.E)‖ < 1 ↔ ‖rhoH D lam τ (σ (a : D.host.E))‖ < 1
      constructor
      · intro h
        rw [← sub_add_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz' h)
      · intro h
        rw [← add_sub_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h (by rw [norm_sub_rev]; exact hz'))
    have h1 := SamePrime.norm_eq hsp y
    have h2 : tauEmb D lam (tauSg D τ) (D.host.conj y) = tauEmb D lam τ (σ y) := by
      unfold tauEmb
      rw [hemb]
    rw [h2, ← coe_rhoH, h1]
    rfl

end GlobalTheory.KerStd
