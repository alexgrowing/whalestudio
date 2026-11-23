import Mathlib
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace GlobalTheory.WithRightAction

noncomputable def withRight {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    (Bs : B.RealPlaceData k r Wp Wq) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (u' : ℕ → ℝ)
    (h : Q.IsType k r Bs.z' π'' u') : B.RealPlaceData k r Wp Wq' :=
  { z := Bs.z, z' := Bs.z', π := Bs.π, π' := π'', μG := Bs.μG, μW := Bs.μW, μN := Bs.μN, μW' := Bs.μW',
    μsec := Bs.μsec, χ := Bs.χ, k_pos := Bs.k_pos, z_mem := Bs.z_mem, z'_mem := Bs.z'_mem, T_pos := Bs.T_pos,
    T'_pos := Bs.T'_pos, π_rep := Bs.π_rep, π'_rep := h.2.1, π_unitary := Bs.π_unitary, π'_unitary := h.2.2.2.1,
    π_cont := Bs.π_cont, π'_cont := h.2.2.1, haarG := Bs.haarG, haarW := Bs.haarW, haarN := Bs.haarN,
    haarW' := Bs.haarW', sec := Bs.sec, χ_smooth := Bs.χ_smooth, χ_supp := Bs.χ_supp, χ_int := Bs.χ_int }

theorem exists_place_other_right_type : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (p : KB.Pl P Wp Wq) (u u' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ), Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) p.T.base.z p.T.base.z' p.T.base.π π'' → 1 ≤ l0 → l0 ≤ P.k → ∃ q : KB.Pl (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) Wp Wq', q.l0 = l0 ∧ q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧ q.T.base.π' = π'' ∧ q.ν' = p.ν' ∧ q.m₀ = p.m₀ ∧ KB.InDDplus2 (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) q.l0 q.T.base Cb q.Θ := by
  obtain ⟨Cb, hCb, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, hCb, ?_⟩
  intro P Wp _ _ _ Wq _ _ _ Wq' _ _ _ p u u' π'' l0 hPl hl1 hl2
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq'
    (withRight p.T.base π'' u' hPl.2.2.2.2.2.2)
  change T.base.z = p.T.base.z at h1
  change T.base.z' = p.T.base.z' at h2
  change T.base.π = p.T.base.π at h3
  change T.base.π' = π'' at h4
  have hPT : Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' := by
    rw [h1, h2, h3, h4]; exact hPl
  have hF : D.IsBaseFrame T.base p.ν' p.m₀ := by
    have := p.hF
    unfold D.IsBaseFrame at this ⊢
    rw [h1, h2]; exact this
  obtain ⟨-, μ, -, -, ⟨-, hμ, -⟩, -⟩ := p.hΘ
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPT
  obtain ⟨L, st, g1, g2, g3, g4, g5, g6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPT X l0
  have hD : P5.IsData (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 :=
    ⟨hPT, hμ, g1, g2, g3, g4, g5, g6⟩
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base p.ν' p.m₀ hF
  obtain ⟨Θ, hI, hC⟩ := hTL Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par)
    T.base.z T.base.z' T.base.π T.base.π' (p.m₀.mulVec p.ν') hPT f1 f2 f3
  exact ⟨⟨l0, T, p.ν', p.m₀, Θ, TP, ⟨hl1, hl2, p.hl.2.2⟩, hN, hF, hPT, ⟨X, μ, L, st, hD, hI⟩⟩,
    rfl, h1, h2, h3, h4, rfl, rfl, hC⟩

end GlobalTheory.WithRightAction
