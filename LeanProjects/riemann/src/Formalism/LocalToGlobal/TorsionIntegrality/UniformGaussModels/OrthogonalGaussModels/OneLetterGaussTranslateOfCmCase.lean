import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussEveryOrth7
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.H (CmOK)

namespace HAux

theorem odd_b {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (hOK : CmOK a₀ b₀ c₀ dK) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := hOK
  rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
  · exfalso
    subst hk
    have h4 : (dK : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by linear_combination -h1
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (dK : ℤ) = 4 * m := ⟨_, h4⟩
    omega
  · exact h

theorem data {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hdK : 0 < dK) (hOK : CmOK a₀ b₀ c₀ dK) :
    Squarefree dK ∧ dK % 4 = 3 ∧ Formalism.L2.Th1.CM.HasCMBy dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) := by
  obtain ⟨j, hj⟩ := odd_b hOK
  have h1 := hOK.1
  refine ⟨hOK.2.2.2.squarefree, by have := hOK.2.2.1; omega, ?_⟩
  intro ω hω
  simp only [PeriodPair.lattice, Formalism.L2.Th1.F.cmPair] at hω ⊢
  rw [Submodule.mem_span_pair] at hω ⊢
  obtain ⟨m, n, rfl⟩ := hω
  refine ⟨-m * j - n * c₀, m * a₀ + n * (j + 1), ?_⟩
  have hs : ((Real.sqrt dK : ℝ) : ℂ) ^ 2 = (dK : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1c : 4 * (a₀ : ℂ) * c₀ = (b₀ : ℂ) ^ 2 + dK := by exact_mod_cast h1
  have hb : (b₀ : ℂ) = 2 * j + 1 := by exact_mod_cast hj
  simp only [Formalism.L2.Th1.CM.omegaK, Formalism.L2.Th1.F.cmTheta, zsmul_eq_mul]
  push_cast
  linear_combination (↑m * ↑a₀ / 2) * hb - ↑n * ((((Real.sqrt dK : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4) * hs +
    (1 / 4) * h1c + ((↑b₀ + Complex.I * ((Real.sqrt dK : ℝ) : ℂ)) / 4) * hb)

end HAux

theorem ThmAEntryEveryH_of (hX : MatrixEntriesCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmAEntryEveryH := by
  unfold ThmAEntryEveryH MatrixEntriesCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem ThmAGaussEveryH_of (hX : GaussFormCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmAGaussEveryH := by
  unfold ThmAGaussEveryH GaussFormCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem OneLetterGaussEveryH_of (hX : OneLetterGaussCMReformulated) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) :
    OneLetterGaussEveryH := by
  unfold OneLetterGaussEveryH OneLetterGaussCMReformulated at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro N0 N1 h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK (Fin N0 × Fin N1) h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF C
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF N0 N1 C _ γ hfr.1 hcurve

theorem KernelEveryH_of (hX : ThreeBoundsCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : CMThetaKernelEveryInertPrime := by
  intro hL hκ a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, tail⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := hN l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := hK hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, ?_⟩
  intro t N hN0 hlN ht σ hσ γ B' hFr F hF ν r0 r1 _ om oms hO hT f f' hH
  exact tail σ hσ F hF ν r0 r1 om oms hO hT n f f' hH _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

theorem ThmSEveryH_of (hX : StructureTheoremCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : ThmSEveryH := by
  intro hL hκ a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := hN l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := hK hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, ?_⟩
  intro t N hN0 hlN ht σ hσ γ B' hFr F hF ν r0 r1 _
  obtain ⟨cS, c1, c2, c3⟩ := tail σ hσ F hF ν r0 r1
  refine ⟨cS, c1, c2, ?_⟩
  intro om oms ϖ μ hϖ hO hT hμ0 hμ f f' hH
  exact c3 om oms ϖ μ hϖ hO hT hμ0 hμ n f f' hH _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

theorem matrix_entries_translate_of_cm_case (hX : MatrixEntriesSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : MatrixEntriesSharpTranslate := by
  unfold MatrixEntriesSharpTranslate MatrixEntriesSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde hx ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde hx ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem gauss_form_translate_of_cm_case (hX : GaussFormSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) : GaussFormSharpTranslate := by
  unfold GaussFormSharpTranslate GaussFormSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF d N0 N1 _ hd2 hde hx ιr _ _ om oms how htr hζ f f' hhyp
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF d N0 N1 hd2 hde hx ιr om oms how htr hζ n f f' hhyp _ γ hfr.1 hcurve

theorem one_letter_gauss_translate_of_cm_case (hX : OneLetterGaussSharpCM) (hN : LTNormExists) (hK : uniformGaussModelConditionEquivalent) :
    OneLetterGaussSharpTranslate := by
  unfold OneLetterGaussSharpTranslate OneLetterGaussSharpCM at *
  intro hLS hKE a₀ b₀ c₀ dK ha hdK hOK l _ h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨hsf, hd4, hcm⟩ := HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, hg2, hg3, hs2e⟩, hrest⟩ :=
    hX dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) hsf hd4 hcm l h5 hld hsq ι g2 g3 ε hgood hε hcoef
  obtain ⟨lam, hlam, hLT⟩ := hN l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 s2 ε c hc hε hg2 hg3 hs2e
  refine ⟨s2, lam, hlam, hs2, hLT, ?_⟩
  intro N0 N1 h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκalg, hκn, hθ⟩ := hK hLS hKE a₀ b₀ c₀ dK ha hdK lam hlam hOK (Fin N0 × Fin N1) h Λ g₀ hLat
  refine ⟨κ, hκ0, hκalg, hκn, fun θ hθmem heq => ?_⟩
  obtain ⟨g₁, hiso, hidx, hK1⟩ := hθ θ hθmem heq l h5 ι
  refine ⟨g₁, hiso, hidx, ?_⟩
  intro t N hN0 hlN hNt σ hσ γ B' hfr F hF C
  have hcurve := hK1 g2 g3 ε s2 hLT hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2.1 hε hcoef t N hN0 hlN hNt σ γ B' hfr
  exact hrest σ hσ F hF N0 N1 C _ γ hfr.1 hcurve

end Formalism.L2.Th1.Top
