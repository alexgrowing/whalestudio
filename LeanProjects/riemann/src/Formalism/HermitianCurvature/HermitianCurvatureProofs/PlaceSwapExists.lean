import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem place_swap_exists : PlaceSwapExists := by
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ p u'' π'' l0 hty hok hl1 hl2
  let Bs : B.RealPlaceData P.k P.r Wp Wq' :=
    { p.T.base with
      π' := π''
      π'_rep := hty.2.1
      π'_unitary := hty.2.2.2.1
      π'_cont := hty.2.2.1 }
  have hN := p.hT 0 (Nat.zero_le _)
  obtain ⟨T', hTb, hTn⟩ := Dx2.Tower.towerExists P.k P.r Wp Wq' Bs hN.1 hN.2.1 hN.2.2
  have hPl : Q.IsPlace (shP P P.u u'') Bs.z Bs.z' Bs.π Bs.π' :=
    ⟨hok, p.hP.2.1, p.hP.2.2.1, p.hP.2.2.2.1, p.hP.2.2.2.2.1, p.hP.2.2.2.2.2.1, hty⟩
  obtain ⟨X⟩ := actual_operators_exist Wp Wq' (shP P P.u u'') Bs.z Bs.z' Bs.π Bs.π' hPl
  obtain ⟨X0, μ, L0, st0, hD0, -⟩ := p.hΘ
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ :=
    level_start_actual Wp Wq' (shP P P.u u'') Bs.z Bs.z' Bs.π Bs.π' hPl X l0
  have hData : P5.IsData (shP P P.u u'') Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hPl, hD0.2.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨Cb, -, hTL⟩ := top_lift_exists
  obtain ⟨Θ, hΘ, -⟩ := hTL Wp Wq' (shP P P.u u'') Bs X μ L st l0 hl1 hl2 hData
  have hfv := HaarMassHermitianCurvature.frameVec_facts p.T.base p.ν' p.m₀ p.hF
  obtain ⟨TP⟩ := type_projectors_exist Wp Wq' (shP P P.u u'') Bs.z Bs.z' Bs.π Bs.π'
    (p.m₀ *ᵥ p.ν') hPl hfv.1 hfv.2.1 hfv.2.2
  have hF : D.IsBaseFrame Bs p.ν' p.m₀ := p.hF
  refine ⟨⟨l0, T', p.ν', p.m₀, Θ, hTb ▸ TP, ⟨hl1, hl2, p.hl.2.2⟩, hTn, hTb ▸ hF, hTb ▸ hPl,
    hTb ▸ ⟨X, μ, L, st, hData, hΘ⟩⟩, ?_, ?_, rfl⟩
  · show T'.base.z = _ ∧ T'.base.z' = _ ∧ T'.base.π = _ ∧ T'.base.μW = _ ∧ T'.base.μN = _ ∧
      T'.base.μW' = _ ∧ p.ν' = _ ∧ p.m₀ = _
    rw [hTb]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show T'.base.π' = π''
    rw [hTb]

end

end Formalism.FourierDecayAlt.P.CutBPEq
