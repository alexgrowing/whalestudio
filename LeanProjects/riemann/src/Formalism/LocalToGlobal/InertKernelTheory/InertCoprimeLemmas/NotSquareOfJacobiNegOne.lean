import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.IntegralSeriesOneLetter

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

theorem oneCopyTh1S_of (h1 : ScaleLTB) (h2 : IsomONB) (h3 : ScaleInt) : OneCopyTh1S := by
  intro D cc δ B hcc hδ p _ h5 hin lam ι hι
  obtain ⟨c, hc, g2, g3, ε, s2, hLT, hg2, hg3, hD, hε, hth, hNR⟩ := h1 D cc δ B hcc hδ p h5 hin ι
  obtain ⟨g₁, e, σ, γ, B', σp, hg, hU, hF, hσp, hONB⟩ := h2 D cc δ B hcc hδ p h5 hin lam ι hι
  refine ⟨c, hc, g2, g3, ε, s2, σp, Fintype.card D.what₂.Tau,
    fun i k => B' k.1 ((Fintype.equivFin D.what₂.Tau).symm i), Fintype.equivFin D.what₂.Tau,
    hLT, hg2, hg3, hD, hε, hth, hσp, hONB, ?_⟩
  intro t N hN hpN ht
  have key := h3 D cc δ B hcc hδ p h5 hin ι c hc g2 g3 ε s2 hLT hg2 hg3 hD hε hth g₁ e hg σ hU (hNR σ hU) γ B' hF
    t N hN hpN ht
  simpa using key

theorem oneCopyLoc_ofS (hLE : LamExt) (hT : OneCopyTh1S) (hC : CoordTie) (hM : ModelTieS) (hR : ReadChangeS) :
    OneCopyLoc := by
  intro D cc δ B hcc hδ p _ hp hin lam
  obtain ⟨ι, hι⟩ := hLE p lam
  obtain ⟨c, hc, g2, g3, ε, s2, σ, r, v, e, hLT, h2, h3, hΔ, hε, hS, hσ, hv, hInt⟩ :=
    hT D cc δ B hcc hδ p hp hin lam ι hι
  refine ⟨σ, r, v, hσ, hv, fun s hs => ?_⟩
  obtain ⟨hpser, N, hN, hNp, hNt⟩ := hC D cc δ B hcc hδ p hp hin lam ι hι s hs
  intro C wq hCm hwq
  obtain ⟨hph0, h, Uu, h0, hhi, h1, hlog, hUu, hexp⟩ :=
    hM D cc δ B hcc hδ p hp hin lam ι hι c hc g2 g3 ε s2 hLT h2 h3 hΔ hε hS C wq hCm hwq
  rw [hpser]
  exact hR D p hp lam B.tor.abelian₂ C wq _ h Uu ((ι c)⁻¹) hph0 h0 hhi h1 hlog hUu hexp r v e _
    (hInt (fun τ => s τ 0 0) N hN hNp hNt)

theorem not_dvd_of_jacobi_neg_one (p : ℕ) [Fact p.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) : ¬ p ∣ d := by
  intro h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod p) = 0 := by
    have : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).2 h
    push_cast; simp [this]
  have hl : legendreSym p (-(d : ℤ)) = 0 := (legendreSym.eq_zero_iff p _).2 h0
  rw [jacobiSym.legendreSym.to_jacobiSym] at hl
  rw [hl] at hj; norm_num at hj

theorem not_square_of_jacobi_neg_one (p : ℕ) [Fact p.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ ∃ a : ZMod p, a ^ 2 = -(d : ZMod p) := by
  rintro ⟨a, ha⟩
  have hne : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hl : legendreSym p (-(d : ℤ)) = 0 := (legendreSym.eq_zero_iff p _).2 h0
    rw [jacobiSym.legendreSym.to_jacobiSym] at hl
    rw [hl] at hj; norm_num at hj
  have hsq : IsSquare ((-(d : ℤ) : ℤ) : ZMod p) := ⟨a, by push_cast; rw [← ha]; ring⟩
  have hl : legendreSym p (-(d : ℤ)) = 1 := (legendreSym.eq_one_iff p hne).2 hsq
  rw [jacobiSym.legendreSym.to_jacobiSym] at hl
  rw [hl] at hj; norm_num at hj

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem scale_lattice_bound : ScaleLTB := by
  intro D cc δ B hcc hδ p _ h5 hj ι
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -⟩ := ReBase.theta_change_of_base D cc δ B hcc
  have hnd := not_dvd_of_jacobi_neg_one p D.host.d hj
  have hin := not_square_of_jacobi_neg_one p D.host.d hj
  obtain ⟨hsq, hmod, hCM⟩ := Formalism.L2.Th1.Top.HAux.data ha hd hcm
  obtain ⟨g2, g3, ε, hgood, hε, hth⟩ := Formalism.L2.Th1.Top.modelInert _ _ hsq hmod hCM p h5 hnd hin ι
  obtain ⟨s2, lam, hlam, -, hLT, hCur, -⟩ :=
    Formalism.L2.DIV.C.hostIntFree a₀ b₀ c₀ _ ha hd hcm p h5 hnd hin ι g2 g3 ε hgood hε hth
  obtain ⟨σ0, F, -, -, -, -, hU0, hF, -⟩ := Formalism.L2.Th1.Top.InhA.joint p h5 1 0 0
  have hc : lam / ((g : ℂ) * δ) ≠ 0 := div_ne_zero hlam hl
  have hL : (Formalism.L2.Th1.F.scalePair B.L (lam / ((g : ℂ) * δ)) hc).lattice =
      (Formalism.L2.Th1.H.cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
    have hB' : B'.L = Formalism.L2.Th1.H.cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl := hIs.1
    ext z
    rw [Formalism.L2.Th1.F.Homog.mem_scale, ← hlat, hB', Formalism.L2.Th1.H.cmL, Formalism.L2.Th1.H.cmL,
      Formalism.L2.Th1.F.Homog.mem_scale, Formalism.L2.Th1.F.Homog.mem_scale]
    have e : ((g : ℂ) * δ)⁻¹ * ((lam / ((g : ℂ) * δ))⁻¹ * z) = lam⁻¹ * z := by
      field_simp
      exact mul_div_cancel_left₀ z hl
    rw [e]
  have hC0 := hCur σ0 F hU0 hF
  obtain ⟨-, hg2, hg3, -, -, -, -, -, hD⟩ := hC0
  refine ⟨lam / ((g : ℂ) * δ), hc, g2, g3, ε, s2, (ReBase.isLTNorm_congr hL p ι g2 g3 s2 ε).2 hLT, hg2, hg3, hD, hε, hth, ?_⟩
  intro σ hU α hα hσα
  exact (hCur σ F hU hF).2.2.2.2.2.2.2.1 α hα hσα

end Formalism.L2.KerInert
