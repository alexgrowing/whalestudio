import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.LettersPoly

noncomputable section

namespace CompanionTheory.WaveGrid.LimSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace

variable {P : M.Par} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wq'] {u u' : ℕ → ℝ}

theorem eigStr_fpmSh [CompleteSpace Wp] (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq))
    (p₀ e₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : KFinDSCoef ε lam f) (hAop : PolyOp e₀ Aop) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A)
    (hD : KDecay P.k P.r ε A h₀) (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → PStar lam (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (fpmSh p f Aop p₀) Y := by
  classical
  obtain ⟨H, i1, i2, i3, σ, Pm, Qm, hlam, hσ, hQ, hP, hfG⟩ := hf
  obtain ⟨n, cf, L, hcf, hAe⟩ := hAop
  set d : ℕ := (2 * P.r + 2) * p₀ + e₀ with hd
  set q : B.Mat P.k P.r → ℂ := fun g => ((Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) with hq
  let ea := stdOrthonormalBasis ℂ Wp
  let eb := stdOrthonormalBasis ℂ Wq
  let φ : Fin (Module.finrank ℂ Wp) → Fin (Module.finrank ℂ Wq) → B.Mat P.k P.r → ℂ :=
    fun a b g => ⟪ContinuousLinearMap.adjoint Pm (ea a), σ g (Qm (eb b))⟫_ℂ
  have hφ : ∀ a b, IsCoef P.k P.r ε lam (φ a b) := fun a b =>
    ⟨H, i1, i2, i3, σ, Qm (eb b), ContinuousLinearMap.adjoint Pm (ea a), hlam, hσ, hQ _, hP _, fun _ _ => rfl⟩
  let F₁ : B.Mat P.k P.r → (Wq' →L[ℂ] Wp) :=
    ∑ i, ∑ a, ∑ b, fun g => (q * cf i * φ a b) g • ((innerSL ℂ (eb b)).smulRight (ea a)).comp (L i)
  have hF₁ : F₁ ∈ ⨆ ν : Box lam (d : ℝ), Wsp P.k P.r Wp Wq' ε ν :=
    Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      smul_mem_iSup (h2 t hZ hZd P.k P.r ε lam h d (q * cf i) (φ a b)
        (mul_mem_letters_pow (h1 P.k P.r _ _ p₀) (polyDeg_mem (hcf i))) (hφ a b) hgap ht) _
  have hFF : ∀ g ∈ B.GV P.k P.r, fpmSh p f Aop p₀ g = F₁ g := by
    intro g hg
    show q g • (f g).comp (Aop g) = F₁ g
    rw [hAe g, ContinuousLinearMap.comp_finsetSum, Finset.smul_sum]
    simp only [F₁, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_smul, op_expand (f g), hfG g hg]
    simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.smul_comp, Finset.smul_sum, Pi.mul_apply,
      smul_smul, φ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, ea, eb, mul_assoc]
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ F₁).1 hF₁
  let e := c.support.equivFin.symm
  have hgν : ∀ ν : Box lam (d : ℝ), PI.ZuckTensor.GapAtLeast ε ν.1 h₀ := fun ν => gap_of_box ν.2 hgap hh
  have hFs : ∀ g ∈ B.GV P.k P.r, fpmSh p f Aop p₀ g = ∑ i, c (e i) g := by
    intro g hg
    rw [hFF g hg, ← hsum, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp e fun ν : c.support => c ν g).symm
  exact ⟨A, c.support.card, fun i => c (e i), fun i y => Formalism.QuantumDeterminants.capP (fun s => ((e i).1.1 s : ℂ)) (y : ℂ), hA,
    fun i => wsp_ckOn hK h3 (hc _), fun i => wsp_inCC hK h4 hD (hgν _) (hc _), hFs,
    fun i y _ => wsp_eig hK h3 h5 _ (hc _), fun i y hy => (norm_capP_le (e i).1.2 y).trans (hnn y hy),
    fun i j hij => wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _) (hgν _)
      (fun hh' => hij (e.injective (Subtype.ext (Subtype.ext hh')))) (hc _) (hc _)⟩

end CompanionTheory.WaveGrid.LimSh
