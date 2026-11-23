import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound

noncomputable section

namespace Formalism.L2.Pj.abelian₂

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {D : D7}

theorem cm_frame_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (P : Frame Y.Ψ r → ℂ) (z0 : Frame Y.Ψ r) (M w : ℝ)
    (hSS : P ∈ Y.SS la) (hM : 0 < M) (hw : (∑ τ, Y.spread la τ) ≤ w) (hw1 : 1 ≤ w) (hr : 0 < r)
    (htr : ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b))
    (hz0 : z0 ∈ Y.dom) (hhalf : ∀ x ∈ Y.dom, Y.pnorm la P x ≤ 2 * Y.pnorm la P z0)
    (hpos : 0 < Y.pnorm la P z0) :
    ∃ (x : Frame Y.Ψ r) (lam : Fin r → Fin r → E), x ∈ Y.dom ∧
      LamBasis Xx (frameBasisRadius r Xx.p0 (fdeg E) (dE E) (Real.sqrt (epStar M (fdeg E) w Xx.k0))
        (3 * frameRadius w r / 5)) (hX ▸ x) lam ∧
      P x ≠ 0 := by
  subst hX
  obtain ⟨x, lam, hx, hL, hP, -⟩ := cm_frame Xx la P z0 M w hSS hM hw hw1 hr htr hz0 hhalf hpos
  exact ⟨x, lam, hx, hL, hP⟩

open Classical in

def LamTieSt (T : Formalism.L2.Pj.Core D) (h : LawsCore T) (j : ℕ) (w : WeightFamilies.Wt D j) (La : ℝ) (aMax : ℕ) : Prop :=
  letI := T.Q.H.starRing
  ∀ (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q)
    (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀) (y : FrPt (T.Q.Xo j) T.Q.c o.K₁)
    (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)), LamPtClauses T j La k x₀ o L σ₁ y eY →
    ∀ F : (recB h).Cusp j w, F ∈ (recB h).Mlat j w → F ≠ 0 → rdU (T.U j T.σ₀) F.1 k x₀.1 ≠ 0 →
    ∃ (a : ∀ b, Fin (L.m b) → ℕ) (G : MvPolynomial (FrVar L.m) o.K₁), G ≠ 0 ∧ (∑ b, ∑ i, a b i) ≤ aMax ∧
      (∀ p, Step5Loc L.e o.Tl.dual o.LamL L.ℓ L.U G w.n p) ∧
      ∀ σ : o.K₁ →+* ℂ, Step5Arch L.e o.Tl.dual o.LamL L.ℓ L.U G a w.n La
        ((recB h).supN j w (σ.comp (algebraMap T.Q.c.F o.K₁)) F) σ

theorem LamLetters.lines {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
    {c : Coeff l} {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La logOm : ℝ} (hG : LamObjGood o f La) (L : LamLetters o)
    (hL : L.IsGood) (hdeg : (∀ k, (o.ℓΨ k).ndeg = logOm / 2) ∧ ∀ k, (o.ℓ' k).ndeg = logOm / 2) :
    (∀ k, (L.ℓ k).Good) ∧ ∀ k, (L.ℓ k).ndeg = logOm / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΨ, h', -⟩ := hG
  have key : ∀ k, (L.ℓ k).Good ∧ (L.ℓ k).ndeg = logOm / 2 := by
    intro k
    have h := hL.2.2.2 k
    rcases hs : L.src k with q | q
    · simp only [hs] at h
      rw [h]
      exact ⟨(hΨ q.2).1, hdeg.1 q.2⟩
    · simp only [hs] at h
      rw [h]
      exact ⟨(h' q.2).1, hdeg.2 q.2⟩
  exact ⟨fun k => (key k).1, fun k => (key k).2⟩

def laOf {T : Formalism.L2.Pj.Core D} {j : ℕ} (Xx : (T.U j T.σ₀).Comp → DataX D.host.E D.R.r) (M wf : ℝ)
    (k : (T.U j T.σ₀).Comp) : ℝ :=
  frameBasisRadius D.R.r (Xx k).p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) wf (Xx k).k0))
    (3 * frameRadius wf D.R.r / 5)

theorem lamw_link (T : Formalism.L2.Pj.Core D) (h : LawsCore T) (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j)
    (w : WeightFamilies.Wt D j) (C A : ℝ) (hM5 : SiegelSpaceAlgebra (E := D.host.E)) (hKey : KeyCore)
    (hLH : ReciprocityTheory.MultiplicativeHeights.LemmaHStatement)
    (Xx : (T.U j T.σ₀).Comp → DataX D.host.E D.R.r) (hX : ∀ k, (Xx k).toData = (T.U j T.σ₀).X k)
    (M wf : ℝ) (hM : 0 < M)
    (hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ wf) (hwf1 : 1 ≤ wf)
    (hr : 0 < D.R.r)
    (htr : ∀ k, ∀ v ∈ (Xx k).L', herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ((T.U j T.σ₀).X k).χ (laU (T.U j T.σ₀) (wtA w) w.n k) γ = 1 ∧
        ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 =
          ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b))
    (hAA : ∀ k, ∀ a ∈ D.host.AA, ∀ v ∈ (Xx k).L', a • v ∈ (Xx k).Λ)
    (aMax : ℕ) (hPt : ∀ La, LamPtSt T j La) (hDeg : LamDegSt T.Q.H large₂.logOm) (hInd : LamIndSt)
    (hTie : ∀ k, LamTieSt T h j w (laOf Xx M wf k) aMax) (hLa1 : ∀ k, 1 ≤ laOf Xx M wf k)
    (hroom : ∀ k, ∀ s : ℕ, s ≤ aMax →
      (pDeg large₂.logOm + (1 / 2) * Real.log (laOf Xx M wf k)) *
          ((s : ℝ) + ((D.R.f * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) * w.n) +
        (s : ℝ) * Real.log ((D.R.r : ℝ) * laOf Xx M wf k) ≤
      WeightFamilies.PP0v D large₂ C A * (1 + Real.log w.size) * w.size) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LAMwAt large₂ (recB h) j w C A := by
  classical
  letI := T.Q.H.starRing
  intro F hF hF0
  have hFC : F.1 ∈ T.C j w := cutR_le T.C j w F.2
  have hhol : rdU (T.U j T.σ₀) F.1 ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F.1).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := holSub_SS hM5 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F.1) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hF1 : F.1 ≠ 0 := fun h0 => hF0 (Subtype.ext h0)
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F.1) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F.1)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F.1 hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F.1) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F.1 k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F.1 k) z0 :=
    fun x hx => (pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F.1 k) z0 := by
    linarith
  obtain ⟨x, lam, hx, hLB, hPx⟩ := cm_frame_of_eq (Xx k) ((T.U j T.σ₀).X k) (hX k) _ _ z0 M wf (hSS k) hM
    (hwf k) hwf1 hr (htr k) hz0 hhalf hposz
  obtain ⟨o, L, σ₁, y, eY, hcl⟩ := hPt (laOf Xx M wf k) h hj k ⟨x, hx⟩ (Xx k) (hX k) (hAA k) lam hLB
  obtain ⟨a, G, hG0, hsa, hloc, harch⟩ := hTie k k ⟨x, hx⟩ o L σ₁ y eY hcl F hF hF0 hPx
  obtain ⟨hGood, hL, hmr, -, -, -, -, -⟩ := hcl
  have hdeg := hDeg T.Q.l T.Q.c (fun _ => rfl) _ _ D.R.f o (laOf Xx M wf k) hGood
  have hdet := hInd D.host.E T.Q.H T.Q.l T.Q.c (fun _ => rfl) _ _ D.R.f o (laOf Xx M wf k) hGood L hL
  obtain ⟨hlg, hnd⟩ := L.lines hGood hL hdeg
  have hGood' := hGood
  obtain ⟨-, -, -, -, -, -, -, -, hgB, -, -, -, -, -, -, -, -, -, hTg, hLg, hkl, hka, -⟩ := hGood'
  have hSpos : ∀ σ : o.K₁ →+* ℂ, 0 < (recB h).supN j w (σ.comp (algebraMap T.Q.c.F o.K₁)) F := by
    intro σ
    rcases ((recB h).supN_nonneg j w (σ.comp (algebraMap T.Q.c.F o.K₁)) F).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (((recB h).supN_eq_zero j w _ F).1 heq.symm) hF0
  have h5 := lambda_lower_bound hKey hLH o.K₁ o.xB o.Tl o.LamL (D.host.E →+* ℂ) L.m L.e L.ℓ L.U G a w.n D.R.r
    (laOf Xx M wf k) large₂.logOm (fun σ => (recB h).supN j w (σ.comp (algebraMap T.Q.c.F o.K₁)) F) hTg hLg hkl hka
    hlg hnd hdet hG0 (hLa1 k) (by exact_mod_cast hr) hmr hSpos hloc harch
  beta_reduce at h5
  have h2 := mean_restrict (K := T.Q.c.F) (L := o.K₁) (fun τ => Real.log ((recB h).supN j w τ F))
  beta_reduce at h2
  rw [h2] at h5
  have h3 : WeightFamilies.meanLogSup (recB h) F = (∑ τ : T.Q.c.F →+* ℂ, Real.log ((recB h).supN j w τ F)) /
      (Module.finrank ℚ T.Q.c.F : ℝ) := by
    rw [WeightFamilies.meanLogSup, NumberField.Embeddings.card T.Q.c.F ℂ]
  rw [h3]
  have hgR : (o.xB.P.g : ℝ) = ((D.R.f * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) := by rw [hgB]
  have hr' := hroom k _ hsa
  rw [hgR] at h5
  linarith

end Formalism.L2.Pj.abelian₂
