import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTopBaseModel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeClauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtRedPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

abbrev algDn (S : Type) [CommRing S] [Algebra d.c₂.F S] : Algebra c.F S :=
  ((algebraMap d.c₂.F S).comp (d.eF : c.F →+* d.c₂.F)).toAlgebra

theorem frBor_down {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} {y₂ y₂' : FrPt d.Xo₂ d.c₂ S} (h : FrOver d y₂ y) (h' : FrOver d y₂' y')
    (hb : FrBor t y₂ y₂') : FrBor t y y' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨ex, bu, b, b₁, b₂, hbs⟩ := hb
  have ex' : y'.x = y.x := by rw [← e', ← e, ex]
  obtain ⟨a, a₁, a₂⟩ := exists_pm (G := Xo.univ.t.G) (x := y.x) (fst (Over.mk y'.x) Xo.univ.t.G).left
    (snd (Over.mk y'.x) Xo.univ.t.G).left (by rw [← ex']; exact pm_cond _)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e'
  obtain rfl : p' = q := pm_ext (p₁'.trans q₁.symm) (p₂'.trans q₂.symm)
  have sq : p' ≫ a = b ≫ p := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, a₁, p₁', Category.assoc, p₁, ← Category.assoc, b₁]
    · rw [Category.assoc, a₂, p₂', Category.assoc, p₂, b₂]
  refine ⟨ex', fun τ i => ?_, a, a₁, a₂, ?_⟩
  · obtain ⟨cf, c₁, c₂, hcf⟩ := bu τ i
    refine ⟨cf, c₁, c₂, ?_⟩
    have := (comb_iff d.m e (fun j => (y₂.tan τ j).1) cf (ex ▸ (y₂'.tan τ i).1)).1 hcf
    rw [funext (hu τ), hu'] at this
    exact this
  · refine (pull_scal_iff a₁ (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S (t none)) y.s y'.s).2
      fun Z r z i hi => ?_
    have er : (r ≫ k) ≫ p' = r := by rw [Category.assoc, hk, Category.comp_id]
    obtain ⟨j, hj⟩ := exists_chart d.Xo₂.univ.t.PP.isLB ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left ((r ≫ k) z))
    have hi₀ : (snd (Over.mk y'.x) Xo.univ.t.G).left (((r ≫ k) ≫ p') z) ∈ Xo.univ.t.PP.L.U i :=
      (congrArg (fun x => (snd (Over.mk y'.x) Xo.univ.t.G).left x ∈ Xo.univ.t.PP.L.U i) (pt_eq er z)).mpr hi
    have hi' : d.m.φ ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left ((r ≫ k) z)) ∈ Xo.univ.t.PP.L.U i :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' ((r ≫ k) z))).mp hi₀
    have k₂ := H' Z (r ≫ k) z i j hi' hj
    have k₁ := (pull_scal_iff b₁ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S (t none)) y₂.s y₂'.s).1 hbs
      Z (r ≫ k) z j hj
    have k₃ := H Z ((r ≫ k) ≫ b) z i j
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq b₁ ((r ≫ k) z))).mpr hi')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq b₁ ((r ≫ k) z))).mpr hj)
    have e2 : r ≫ a = ((r ≫ k) ≫ b) ≫ p := by
      calc r ≫ a = ((r ≫ k) ≫ p') ≫ a := by rw [er]
        _ = (r ≫ k) ≫ (p' ≫ a) := Category.assoc _ _ _
        _ = (r ≫ k) ≫ (b ≫ p) := by rw [sq]
        _ = ((r ≫ k) ≫ b) ≫ p := (Category.assoc _ _ _).symm
    have e3 : (r ≫ a) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
        ((r ≫ k) ≫ b) ≫ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left := by
      calc (r ≫ a) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = r ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left := by
            rw [Category.assoc, a₂]
        _ = ((r ≫ k) ≫ p') ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left := by rw [er]
        _ = (r ≫ k) ≫ (fst (Over.mk y₂'.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc, p₂']
        _ = ((r ≫ k) ≫ b) ≫ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc (r ≫ k) b, b₂]
    have e4 : ((r ≫ k) ≫ b) ≫ (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left =
        (r ≫ k) ≫ (snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc, b₁]
    rw [e3, e2, k₃, e4]
    conv_lhs => rw [← er]
    rw [k₂, k₁, mul_left_comm]

theorem below_exists (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {S : Type} [CommRing S]
    [Algebra c.F S] [Algebra d.c₂.F S] (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a)
    (y₂ : FrPt d.Xo₂ d.c₂ S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  refine GlobalTheory.ClassSumCompare.exists_frUnder d hc y₂ ?_
  rw [Category.assoc, hO hK, ← Category.assoc, y₂.x_over]
  unfold sOf
  rw [GlobalTheory.ClsVal.Cmp.spMap_comp']
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  rw [← hc]
  exact congrArg _ (Subtype.ext rfl)

open Classical in

def pullRule (f : Rul Xo c) : Rul d.Xo₂ d.c₂ := fun p u =>
  letI := algDn d p.R
  if h : ∃ y : FrPt Xo c p.R, FrOver d u y then evR Xo c f h.choose else 0

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

instance tRing_reduced {K : Type} [Field K] (p : TRing K) : IsReduced p.R :=
  (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

theorem wtRed (Xo : Moduli Dw l) (c : Coeff l) : ReciprocityTheory.ChartRestriction.G.PullbackSections.WtRed Xo c :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.wtRed_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c)
    (GlobalTheory.borDesc_and_wtField _ _ _ _ Xo c).2 (GlobalTheory.framedPoint_baseChange_clauses _ _ _ _ Xo c).2.2.2

theorem pullRule_eq (f : Rul Xo c) (p : TRing d.c₂.F) (u : FrPt d.Xo₂ d.c₂ p.R) :
    letI := algDn d p.R
    ∀ y : FrPt Xo c p.R, FrOver d u y → pullRule d f p u = evR Xo c f y := by
  let _ := algDn d p.R
  intro y hy
  have h : ∃ y : FrPt Xo c p.R, FrOver d u y := ⟨y, hy⟩
  unfold pullRule
  rw [dif_pos h, GlobalTheory.ClassSumCompare.frUnder_unique d h.choose_spec hy]

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem pullRule_mem (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a m) : pullRule d f ∈ sec d.Xo₂ d.c₂ a m := by
  refine ⟨fun p q φ u u' hm => ?_, fun p t u u' hb => ?_⟩
  · letI := algDn d p.R
    letI := algDn d q.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := q.R) (fun _ => rfl) u'
    let φc : p.R →ₐ[c.F] q.R := ⟨φ.toRingHom, fun a => φ.commutes (d.eF a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R q.R φc y
    have hw' : FrOver d u' w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hy hw hm
    obtain rfl : y' = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy' hw'
    show pullRule d f q u' = φ (pullRule d f p u)
    rw [pullRule_eq d f q u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc y
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R y) y' hw
  · letI := algDn d p.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u'
    show pullRule d f p u' = wchar (ex Dw a m) t * pullRule d f p u
    rw [pullRule_eq d f p u' y' hy', pullRule_eq d f p u y hy]
    exact wtRed Xo c a m f hf p.R t y y' (frBor_down d hy hy' hb)

theorem evR_pullRule (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a m) {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hc : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k)
    (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ (pullRule d f) y₂ = evR Xo c f y := by
  have key : ∀ (p : TRing d.c₂.F) (φ : p.R →ₐ[d.c₂.F] k) (u : FrPt d.Xo₂ d.c₂ p.R), FrMap φ u y₂ →
      φ (pullRule d f p u) = evR Xo c f y := by
    intro p φ u hu
    letI := algDn d p.R
    obtain ⟨z, hz⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    let φc : p.R →ₐ[c.F] k := ⟨φ.toRingHom, fun a => (φ.commutes (d.eF a)).trans (hc a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R k φc z
    have hw' : FrOver d y₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hz hw hu
    obtain rfl : y = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy hw'
    rw [pullRule_eq d f p u z hz]
    exact (GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc z
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R z) y hw).symm
  have hT := GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂
  have e : evR d.Xo₂ d.c₂ (pullRule d f) y₂ =
      hT.choose_spec.choose (pullRule d f hT.choose hT.choose_spec.choose_spec.choose) := by
    unfold evR evalAt
    rw [dif_pos hT]
  rw [e]
  exact key _ _ _ hT.choose_spec.choose_spec.choose_spec

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead

theorem exists_pull : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ),
    ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ := by
  intro D T hT j hj σ _ C _ a n f hf
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  obtain ⟨hf', hv⟩ := (GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ C.hle).1 a n f hf
  refine ⟨pullRule C.d (GlobalTheory.FieldBC.rulBC C.hle f), pullRule_mem C.d hO hK hf', ?_⟩
  intro k _ _ _ _ h hc y₂ y hy
  rw [evR_pullRule C.d hO hK hf' hc y₂ y hy, hv k h y]

end GlobalTheory.CovPull
