import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameMove

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_mono {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (hmn : m ≤ n) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : CongAt (F := F) P n k) : CongAt (F := F) P m k := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have e0 : (((qOf P : ℕ) : E) ^ m)⁻¹ = algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m)) * (((qOf P : ℕ) : E) ^ n)⁻¹ := by
    rw [map_pow, map_natCast]
    have hn : ((qOf P : ℕ) : E) ^ n = ((qOf P : ℕ) : E) ^ m * ((qOf P : ℕ) : E) ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hn]
    field_simp
  have e : iA F E (((qOf P : ℕ) : E) ^ m)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
      iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m))) *
        (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, ← map_mul, e0]
  rw [e]
  exact GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int _) (h a b)

end Cong

theorem mem_of_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (k : Sp E n ≃ₗ[E] Sp E n) (hk : ∀ x ∈ stdAt E n P, ((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x) ∈ stdAt E n P)
    (x : Sp E n) (hx : x ∈ stdAt E n P) : k x ∈ stdAt E n P := by
  have hq : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hc : ((qOf P ^ d : ℕ) : E) ≠ 0 := by exact_mod_cast pow_ne_zero d hq
  have e : k x = x + (qOf P ^ d) • (((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x)) := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
  rw [e]
  exact add_mem hx (nsmul_mem (hk x hx) _)

end GlobalTheory.FrameMove

namespace GlobalTheory.FrameMove

theorem frames_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ j hj β x x₁ κ p p₁ hxκ hp hp₁ P dep g hd1 hdD hg hIn
  have hD1 : 1 ≤ (t.cst μ).D P := hd1.trans hdD
  have hu := hp.frame P
  have hu₁ := hp₁.frame P
  unfold NearAt at hu hu₁
  unfold InFrame NearAt at hIn
  rw [hxκ] at hu₁
  set h := (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) with hh
  have hs : h = g⁻¹ * ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) := by
    ext w; rfl
  have key : ratA D.host.F (seamGL t.seam h) =
      ((ratA D.host.F (seamGL t.seam g))⁻¹ *
        ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))⁻¹ *
        ratA D.host.F (seamGL t.seam g)) *
      (((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam g))⁻¹ *
      ((ratA D.host.F (A.crd j hj) * (x.1 * κ) * ratA D.host.F (A.fb j hj β P))⁻¹ *
        ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    group
  have c1 := GlobalTheory.CplPt.congAt_conj (dep P)
    (congAt_mono hdD (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hD1 hu))
    (fun a b => GlobalTheory.CplPt.seamGL_int t.seam ⟨g, hg⟩ a b)
  have c2 := GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hIn
  have c3 := congAt_mono hdD hu₁
  have hC : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h)) := by
    rw [key]
    exact GlobalTheory.CplPt.congAt_mul _ (GlobalTheory.CplPt.congAt_mul _ c1 c2) c3
  have hCi : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h⁻¹)) := by
    rw [map_inv, map_inv]
    exact GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hC
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h hC
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h⁻¹ hCi
  refine ⟨fun w => ⟨fun hw => ?_, fun hw => mem_of_local P.1 (dep P) h l1 w hw⟩, fun w hw => ?_⟩
  · have := mem_of_local P.1 (dep P) h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (h w) = w from h.symm_apply_apply w] at this
  · have := l1 w hw
    rwa [Nat.cast_pow] at this

end GlobalTheory.FrameMove
