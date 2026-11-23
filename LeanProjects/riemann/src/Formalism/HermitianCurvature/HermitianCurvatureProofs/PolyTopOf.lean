import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOnHOfLoc

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ae_left {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
      (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
  have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
  filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩

theorem polyTop_of (hKA : KrAA) : PBN.PolyTop := by
  intro Wp Wq _ _ _ _ _ _ P p G s h t hs hq hG
  set q : C.LPt := h ++ [(s, t)] with hqdef
  set Bs := p.T.base with hBs
  by_cases hpos : D.IsLocPt q (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r q
  · by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r Bs.z Bs.z' γ = D.ptMatN q (P.r + 1) ∧ D.IsDFrame Bs p.ν' p.m₀ γ
    · obtain ⟨θL, hsplit⟩ := vecV_split Bs p.ν' p.m₀ q hpos h'
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r Bs.z Bs.z' q h'.choose hpos.1 hZ
      have hposG : 0 < Gf P.k P.r Bs.z Bs.z' h'.choose := hGq ▸ hpos.2
      set κ : ℂ := (-1) ^ (s - 1) / t with hκ
      have hA : ∀ y : ℝ, KB.CptCoef Bs (PBN.aaTop Bs y G) := fun y => Formalism.FourierDecayAlt.P.raising_compact_support P.k P.r Wp Wq Bs G y hG
      obtain ⟨c, hc, hcy⟩ := poly_integral (Bs.μW.prod Bs.μN) (D.ptSize h)
        (fun y x => lint Bs h'.choose θL (PBN.aaTop Bs y G) x) (fun x => κ • lint Bs h'.choose θL G x)
        (fun y => (hsplit _ (hA y)).1)
        (by
          filter_upwards [ae_left Bs] with x hx
          obtain ⟨c, hc, hcy⟩ := pt_poly hKA Bs hG h s t hs hq hγ hZ hposG hx
          set a : ℂ := ((θL x : ℝ) : ℂ) * psi P.k P.r Bs.z cStd (Matrix.of x.2) with ha
          set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bs.π (Matrix.of x.1)) with hL
          refine ⟨fun n => a • L (c n), ?_, fun y => ?_⟩
          · simp only
            rw [hc, map_smul, smul_comm]
            rfl
          · show a • L (PBG.Kr Bs (PBN.aaTop Bs y G) _) = _
            rw [hcy y, map_sum, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro n _
            rw [map_smul, smul_comm])
      refine ⟨c, ?_, fun y => ?_⟩
      · rw [hc, integral_smul, ← (hsplit G hG).2]
        rfl
      · show D.vecV Bs p.ν' p.m₀ (PBN.aaTop Bs y G) q = _
        rw [(hsplit _ (hA y)).2, hcy y]
    · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
      · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
        unfold D.vecV
        rw [dif_pos hpos, dif_neg h', smul_zero]
      · show D.vecV Bs p.ν' p.m₀ _ q = _
        unfold D.vecV
        rw [dif_pos hpos, dif_neg h']
        simp
  · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
    · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
      unfold D.vecV
      rw [dif_neg hpos, smul_zero]
    · show D.vecV Bs p.ν' p.m₀ _ q = _
      unfold D.vecV
      rw [dif_neg hpos]
      simp

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
