import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetOfPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistBaseChangeOfFinrankSectionsOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesConv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefVal

theorem summable_coef : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u _ k hk s g w hw
  have hTW : TwistBCSpanStatement := twistBCSpan_of (GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  obtain ⟨v, hvn⟩ := PadicVal.exists_addValuation _ h0 h1
  have hv : ValOver ϖ (PadicAlgCl p) v := fun c n hc => by
    have e := PsiForm.norm_of_hasVal u.norm_le hϖ hc
    obtain ⟨q, hq, hq'⟩ := hvn (algebraMap _ _ c) (norm_pos_iff.1 (by rw [e]; exact Real.exp_pos _))
    rw [e, Real.log_exp, neg_mul, neg_neg, mul_comm, mul_left_inj' (Real.log_neg h0 h1).ne] at hq'
    have : q = n := by exact_mod_cast hq'.symm
    rw [hq, this]
  have ht : Filter.Tendsto (fun χ => coef s g w χ) Filter.cofinite (nhds 0) := by
    refine PadicVal.tendsto_of_null h0 h1 hvn fun q => ?_
    obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q :=
      WithTop.coe_lt_coe.1 ((le_v_coef hw (hr χ) (hl χ) hω).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith
  obtain ⟨T, hT⟩ := CoefField.exists_finset hLL.1.globalFns hk s g hw fun α => by
    obtain ⟨r, n, a, σ, σF, hσ, -, hsum⟩ := exists_vge hϖ hv hTW hk (s.s α)
    exact ⟨n, a, σ, σF, hσ, hsum⟩
  obtain ⟨-, -, -, K₀, hK₀, hK⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hm : ∀ χ, coef s g w χ ∈ K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p)) :=
    hT (K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))).toSubfield
      (fun a => (le_sup_left : K₀ ≤ _) (show _ ∈ (K₀ : Set (PadicAlgCl p)) from hK ▸ ⟨a, rfl⟩))
      (fun t h => (le_sup_right : _ ≤ K₀ ⊔ _) (IntermediateField.subset_adjoin _ _ h))
  exact ⟨PadicVal.summable_of_mem _ hm ht, ht, _, inferInstance, hm⟩

end GlobalTheory.ZH.SeriesConv
