import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_div_torsion : ∀ (X₁ : GlobalTheory.GSep.GSet) (z : X₁.M.Z) (k : ℕ), 2 ≤ k → k ∣ X₁.S.r * X₁.S.N →
    ∃ a : X₁.S.Gam, k • a = 0 ∧ X₁.M.Div X₁.S.th a z := by
  intro X z₀ k hk hd
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z, hz', hcl⟩ := (isClosed_closure (s := {z₀})).exists_closed_singleton ⟨z₀, subset_closure rfl⟩
  have hsp : z₀ ⤳ z := specializes_iff_mem_closure.2 hz'
  obtain ⟨U, hne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X
  obtain ⟨p, _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z hcl U hne
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hTU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hle : X.S.R ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hU _ (hyU ⟨_, rfl⟩)
  have hsw : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (closedPoint (PadicAlgCl p)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]
  let y₀ : X.S.R →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ y) _ hsw).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.S.R, y₀ a = X.M.val (gPt p ≫ y) a := fun _ => rfl
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ X.S.R a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hy ((X.M.O z).algebraMap_mem a)
  obtain ⟨u, l, τ, hτ, -⟩ :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hTU hL hL2 hUT X.o₁ X.Ω₁ X.S X.ρ).2 p y₀ ∅ hint
  have hq : ∀ w, 0 ≤ l.q w := fun w => by
    obtain ⟨e, he, -⟩ := hτ
    have h := τ.q_nonneg (e.symm w)
    rwa [he, AddEquiv.apply_symm_apply] at h
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale hL hL2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ _ X.ρ p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    exact hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (hq w) (by positivity)))))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, RatModel.Div.of_specializes ?_ hsp⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hy (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hy
  have e : ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ =
      ‖y₀ ⟨X.S.th d, X.S.th_mem d⟩‖ * ‖X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul hsw (hle (X.S.th_mem d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have b₁ := RatModel.norm_val_le_one hy (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)))
  nlinarith

end GlobalTheory.GSep
