import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem chord_of : ExpTw → SqIntCrit → Chord := by
  intro hTw hSq E _ _ _ r s hr hs V c T lam hlam hT hp hb φ hφ k g
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hdR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hd
  unfold pE at hp
  push_cast at hp
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.left φ hφ k g m₂
    refine ⟨mulChi r (Model.absC E (-(c / (r * (Module.finrank ℚ E : ℂ))))) ψ₀, haut.mulChi _, ?_,
      fun m₁ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E r _ (haut.mulChi _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₁ h1 h2 c₁ hc₁
      have h3 := hexp r₁ h1 h2 _ (hTw E r ψ₀ _ haut r₁ h1 h2 c₁ hc₁)
      have h4 := hb r₁ h1 (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.left_eq _ _ _ _ _ hr.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.left_arith r s r₁ _ lam _ _ (by exact_mod_cast hr) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.right φ hφ k g m₁
    refine ⟨mulChi s (Model.absC E (-(-c / (s * (Module.finrank ℚ E : ℂ))))) ψ₀, haut.mulChi _, ?_,
      fun m₂ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E s _ (haut.mulChi _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₂ h1 h2 c₂ hc₂
      have h3 := hexp r₂ h1 h2 _ (hTw E s ψ₀ _ haut r₂ h1 h2 c₂ hc₂)
      have h4 := hb (r + r₂) (by omega) (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.right_eq _ _ _ _ _ hs.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.right_arith r s r₂ _ lam _ _ (by exact_mod_cast hs) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4

end PositivityTheory.Rg.Rs
