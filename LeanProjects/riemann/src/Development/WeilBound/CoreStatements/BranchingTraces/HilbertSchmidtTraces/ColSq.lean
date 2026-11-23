import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace

namespace HilbertSchmidtTraceGeometry

theorem _root_.PositivityTheory.UnitaryDecomposition.X4.emb : (∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → ∃ ι : UJ ε' →* UJ ε, (∀ h, umat (ι h) = emb e (um h)) ∧ IsStdStab ε ε' ι (Pi.single (zi e) 1) ∧ ∀ h : Matrix (Fin n) (Fin n) ℂ, incl e * h * (incl e)ᴴ + vecMulVec (Pi.single (zi e) (1 : ℂ)) (star (Pi.single (zi e) (1 : ℂ) : Fin (n + 1) → ℂ)) = emb e h) ∧ (∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m), nsq (g *ᵥ Pi.single j 1) = colSq g j) ∧ (∀ {m : ℕ} (ε : Fin m → Bool) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), IsURepOn (UJset ε) π → IsU (onU ε π)) ∧ ∀ {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)), μ.IsHaarMeasure → IsHCParam lam → IsDS ε lam π → μ.IsMulRightInvariant ∧ (∃ d, IsFdeg μ π d ∧ IsFd μ (onU ε π) d) ∧ ∃ v ∈ lowKSub ε lam π, ‖v‖ = 1 := by
  refine ⟨fun {n} ε ε' e hF => ?_, fun g j => ?_, fun ε A _ _ π hU => ?_, fun {m} ε lam A _ _ π μ hμ _ hπ => ?_⟩
  · have key : ∀ h : Matrix (Fin n) (Fin n) ℂ, GlobalTheory.CompanionTheory.PairingAnalysis.emb e h * incl e = incl e * h := fun h => by
      ext a b
      obtain ⟨a, rfl⟩ := e.surjective a
      rw [mul_apply, mul_apply, ← e.sum_comp]
      rcases a with a | a <;> simp [GlobalTheory.CompanionTheory.PairingAnalysis.emb, incl]
    have h1 : ε (e (Sum.inr ())) = true := hF.1
    refine ⟨⟨⟨PositivityTheory.UnitaryDecomposition.embU hF, Subtype.ext (Units.ext PositivityTheory.UnitaryDecomposition.emb_one)⟩,
      fun a b => Subtype.ext (Units.ext (PositivityTheory.UnitaryDecomposition.emb_mul _ _))⟩, fun _ => rfl, ⟨incl e, ⟨rfl, ?_, ?_, ?_, fun h => key _, fun h => ?_⟩,
      ?_, ?_, ?_⟩, fun h => ?_⟩
    · ext a b
      simp only [Jm, mul_apply (M := _ * _), mul_diagonal]
      rw [← e.sum_comp]
      by_cases hab : a = b
      · subst hab; simp [incl, hF.2]
      · simp [incl, hab, Ne.symm hab]
    · funext a
      simp [Jm, incl, zi]
    · simp [Jm, zi, h1]
    · funext a
      rw [mulVec_single_one]
      exact (PositivityTheory.UnitaryDecomposition.emb_col _ a).trans (by rw [Pi.single_apply]; exact if_congr Iff.rfl rfl rfl)
    · ext a b
      rw [mul_apply, ← e.sum_comp]
      simp [incl, one_apply, eq_comm]
    · funext a
      simp [incl, zi]
    · simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, Pi.single_apply, apply_ite]
    · rw [← key]
      ext a b
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [key]
      rcases a with a | a <;> rcases b with b | b <;>
        simp [GlobalTheory.CompanionTheory.PairingAnalysis.emb, incl, mul_apply, vecMulVec_apply, zi, Pi.single_apply]
  · simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, colSq]
  · exact ⟨hU.1.1, fun a b => hU.1.2 _ a.2 _ b.2, fun g => hU.2.1 _ g.2, (PositivityTheory.UnitaryDecomposition.uRep_self hU).cont⟩
  · have := hπ.1
    obtain ⟨κ, hκ, hS⟩ := PositivityTheory.UnitaryDecomposition.schur_haar hπ μ
    have hd : IsFdeg μ π κ⁻¹ := ⟨inv_pos.2 hκ, fun v w v' w' => ⟨(hS v w v' w').1, (hS v w v' w').2.trans (by
      push_cast; rw [div_inv_eq_mul, mul_comm])⟩⟩
    refine ⟨?_, ⟨_, hd, hd⟩, ?_⟩
    · have : (muG ε).IsMulRightInvariant := by
        rw [← Measure.inv_eq_self (muG ε)]; infer_instance
      rw [Measure.isMulLeftInvariant_eq_smul μ (muG ε)]
      infer_instance
    · obtain ⟨S, hS⟩ := hπ.2.2.2.2.2.1
      obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      exact ⟨(‖v‖⁻¹ : ℂ) • v, Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε π (lowK ε lam) S}) hS hv),
        norm_smul_inv_norm (𝕜 := ℂ) hv0⟩

end HilbertSchmidtTraceGeometry
