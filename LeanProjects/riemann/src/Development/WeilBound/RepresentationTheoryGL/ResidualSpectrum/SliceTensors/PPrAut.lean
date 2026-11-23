import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspStab

namespace PositivityTheory.Rg.Rs.PrAut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem isAutForm_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ) :
    IsAutForm (act o φ) := by
  cases o with
  | fin k =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
      rw [mul_assoc, h.left]
    · have e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ} := by
        ext k'
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E N k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E N k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}
      rw [e]
      exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map
        (finRep E N k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin
    · obtain ⟨C, M, h1⟩ := h.growth (g * finGL E N k)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
  | cpt c =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))
      rw [mul_assoc, h.left]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (cptRep E N c φ) = cptRep E N c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E N c' * cptRep E N c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin
    · obtain ⟨C, M, h1⟩ := growth_mul (Unitary.toUnits c) (h.growth g)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
  | lie X =>
    refine ⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin,
      zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin,
      GlobalTheory.CuspStab.lie_growth hF E N X φ h⟩
    · change lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, h.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (lie E N X φ) = lie E N X φ
        change (rt E N (finGL E N k) * lie E N X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E N X) hk

end PositivityTheory.Rg.Rs.PrAut

end
