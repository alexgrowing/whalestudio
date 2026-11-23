import Formalism.WachLatticeTwists.SplitClassesAll.HZeroFromWFull
import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.H0WeightInvariants

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology Formalism.RepresentationBoundsCohomology.JT Polynomial

theorem tbWFull : StatTBWFull := by
  intro ℓ _ R r L En M0 h0 W U A Y' F hX hA hY1 hY2 hHT e d D X infm infX K T φ ψ hd hin hLES hT5 hCR
    hK hTI hT4 hT3 htf Gs _ _ _ M _ _ _ _ _ _ MB _ _ _ _ _ aM aB Fj Hs γs lg ε iGe iB Os _ _ cupL embB
    hlg hadd hH hgen hγ hsq hcup hpin hLa hRV _ _ _ _ exQ Hfs δ hexQ hcompat hspan hdim hLu hcorF hcr
    hC hL hdR hH2
  obtain ⟨hv, hm1, hm2, _⟩ := w_facts R F
  obtain ⟨_, _, _, hsm⟩ := genM ℓ (R.χ R.γ) R.s (M0 + h0) F.s1 F.s2 F.valγ
  have hRec : D.Recip (beta ℓ R.s e) := recip ℓ D R.s e Os cupL F.s1 htf hLa hRV

  have hlog : ∀ x, ((ℓ : ℤ_[ℓ]) ^ (R.s + ceilE ℓ e)) • D.bW (D.gE (T.infm x)) ∈ D.La0 := by
    intro x
    obtain ⟨c, hc1, hc2, hc3, hc4⟩ := hpin x
    obtain ⟨y', ⟨y, rfl⟩, c'', hc'', heq⟩ := class_of_w_zero_in_H1 ℓ Gs M MB aM aB Fj Hs γs lg ε R.s (ceilE ℓ e)
      (LinearMap.range embB) c hlg hadd hH hgen hγ hc2 hc3 hc4
    obtain ⟨c', hc', hcl⟩ := hcup y
    have : c' = c'' := by
      apply Subtype.ext
      funext σ
      rw [hc', hc'']
    rw [hLa]
    refine ⟨y, ?_⟩
    apply iB.injective
    rw [hcl, this, ← heq, hc1, map_smul, hsq]

  have hCor : D.Cor d := by
    refine ⟨hcr, fun z hz => hcorF z ?_⟩
    set k : ℕ := (-(beta ℓ R.s e)).toNat with hk
    set n : ℕ := ((k : ℤ) + beta ℓ R.s e).toNat with hn
    have hn' : (n : ℤ) = k + beta ℓ R.s e := by
      rw [hn, Int.toNat_of_nonneg]
      have := Int.self_le_toNat (-(beta ℓ R.s e))
      omega
    have hℓ0 : ((ℓ : ℚ_[ℓ]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
    refine kerExp ℚ_[ℓ] D.HV D.HB exQ Hfs δ (D.La0 : Set D.HB) ((ℓ : ℚ_[ℓ]) ^ n) hℓ0 hspan ?_ hdim hLu z
      (by rw [hexQ, hz])
    intro y hy
    obtain ⟨z', hz'⟩ := hRec y k n (D.La0.smul_mem _ hy) hn'
    refine ⟨D.jW z', ?_⟩
    rw [hexQ, ← hz', ← hcompat]
    push_cast
    rfl
  exact ⟨F.s1, F.s2, hsm, F.valγ, hv, hd,
    (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)), K, T, φ, ψ,
    (fun k => pieceWThm ℓ R r L En M0 h0 W U A Y' F hX hA hY1 hY2 hHT (0 + k) (infm k) (infX k)
      (hin k).2.1 (hin k).2.2), hLES, hT5, hCR, hK, hTI, hT4, hT3, htf, hlog, hC, hL, hdR, hH2, hRec, hCor⟩

theorem h_zero_from_w_full : HZeroFromWFull := by
  intro ℓ _ R r L En M0 h0 W A Y' F FH hA hY1 hY2 ρ Sτ Pp Sp Cm Bm Uτ hX hP hS hB hHT h0U hne infm infX X
    hInf hT4 hUn hFl hLES
  obtain ⟨hv, hm1, hm2, _⟩ := w_facts R F
  have hI := wInter ℓ R r L En M0 h0 W A F hA
  have hVm := w3Vm ℓ R r L En M0 h0 W F
  have hinjO : Function.Injective R.eOh := by
    intro a b hab
    have := FH.injE hab
    rw [← R.Tt.pr_alg a, this, R.Tt.pr_alg]
  obtain ⟨s1, s2, s3, s4, s5⟩ := sec3 ℓ R.Gg R.OC R.Tt.Om R.eOh R.actO r ρ (L.sl R.actO) Sτ (UmW R L W)
    (VmW R L W) (A.map R.ϑ) Y' Pp Sp Cm Bm (R.z * R.ϖ) F.lnzd hinjO hI hY2 hP hS hB hVm
  have hPiece := pieceBThm ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT 0 infm infX
    hInf hT4
  have hCB : Cm.map R.eOh * Bm.map R.eOh = 1 := by
    rw [← Matrix.map_mul, s4, Matrix.map_one _ (map_zero _) (map_one _)]
  have hzero := cyclotomicInvariantsZero_statement ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT h0U FH.t4
    FH.injE FH.g0E
    (by
      intro h hh
      show (Cm.map R.eOh).map (R.actO (R.p h)) * UmW R L W (R.p h) * Bm.map R.eOh = 1
      rw [umH ℓ R r L En M0 h0 W F FH h hh, Matrix.mul_one]
      have : (Cm.map R.eOh).map (R.actO (R.p h)) = Cm.map R.eOh := by
        ext a b
        exact FH.fixOi h hh _
      rw [this, hCB])
    (by
      show (Cm.map R.eOh).map (R.actO (R.p R.gg)) * UmW R L W (R.p R.gg) * Bm.map R.eOh = _
      have e1 : (Cm.map R.eOh).map (R.actO (R.p R.gg)) = Cm.map R.eOh := by
        ext a b
        show R.actO (R.p R.gg) (R.emb (algebraMap R.Tt.Om R.Tt.Oi (Cm a b))) = _
        rw [FH.g0E, AlgHom.commutes]
        rfl
      have e2 : UmW R L W (R.p R.gg) = (VmW R L W).map R.eOh := umVm ℓ R r L En M0 h0 W F
      rw [e1, e2, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl)
  refine ⟨hm1, fun _ => hm2, hv, h0U, hne, hPiece, hUn, hFl, hLES, ⟨?_, ?_⟩⟩
  · intro x _ _
    exact Subtype.ext (hzero x.1 x.2)
  · intro x
    exact ⟨map_zero _, map_zero _⟩

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
