import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPoint
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.BcExAll
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

open GlobalTheory.CompanionTheory.Ar.Rec.FinRd GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue
open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique)

section HV

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

theorem aeval_conj (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    MvPolynomial.aeval (fun p => starRingEnd ℂ (z p)) g = starRingEnd ℂ (MvPolynomial.aeval z g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

theorem hv_conj {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {w : ℂ} (h : Small.HasVal y a s z w) :
    Small.HasVal y a s (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, e, ?_, ?_⟩
  · rw [aeval_conj]
    exact (map_ne_zero _).2 hz0
  · rw [aeval_conj, aeval_conj, ez, map_mul]

theorem ptsOver_conj {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (h : z ∈ Small.ptsOver ℂ P) :
    (fun p => starRingEnd ℂ (z p)) ∈ Small.ptsOver ℂ P :=
  ⟨fun k => (h.1 k).imp fun _ hi => (map_ne_zero _).2 hi, fun f hf => by rw [aeval_conj, h.2 f hf, map_zero]⟩

theorem ptsOver_of_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P :=
  ⟨h.1, fun f hf => by
    have := h.2 f hf
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this⟩

theorem valAt_of_hasVal {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {zC : Spec (CommRingCat.of ℂ) ⟶ X}
    {z : (Σ k, ι k) → ℂ} (hp : z ∈ Small.ptsOver ℂ (mCoordIdeal y)) (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre zC)
    (hc : CoordsAt ξ y zC z) {s : Ω} {w : ℂ} (h : Small.HasVal y 0 s z w) : ValAt ξ zC s w := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  have hdd : dg = dh := funext fun k => by have := hd k; simp at this; exact this
  subst hdd
  choose cc hcc using hc.1
  have hc' : ∀ k, z ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hM : (∏ k, y ⟨k, cc k⟩ ^ dg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc.2 k (cc k) (hcc k)).1
  have hMw : (∏ k, z ⟨k, cc k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
  have hfy : MvPolynomial.aeval y f ≠ 0 := fun h0 => hz0 (hp.2 f (by
    show mConeMap y f = 0
    rw [Small.ReadFinTest.mConeMap_form y hf, h0]
    simp))
  have := CxVal.mul (GlobalTheory.CompanionTheory.Ar.PB.valAt_form hc hz hc' hg)
    (CxVal.inv (GlobalTheory.CompanionTheory.Ar.PB.valAt_form hc hz hc' hf) (div_ne_zero hz0 hMw))
  convert this using 1
  · rw [e]; field_simp
  · rw [ez]; field_simp

theorem hv_mono {z : (Σ k, ι k) → ℂ} (hp : z ∈ Small.ptsOver ℂ (mCoordIdeal y)) (ch : ∀ k, ι k)
    (hy : ∀ k, y ⟨k, ch k⟩ ≠ 0) (hz : ∀ k, z ⟨k, ch k⟩ ≠ 0) (d : K → ℤ) :
    Small.HasVal y d (∏ k, y ⟨k, ch k⟩ ^ d k) z (∏ k, z ⟨k, ch k⟩ ^ d k) := by
  classical
  have hsingle : ∀ k, Small.HasVal y (Pi.single k 1) (y ⟨k, ch k⟩) z (z ⟨k, ch k⟩) := fun k =>
    ⟨Pi.single k 1, 0, MvPolynomial.X ⟨k, ch k⟩, 1, TiePrimes.homog_X _, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one,
      fun j => by
        by_cases hj : j = k
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj], by simp, by simp, by simp⟩
  have := hv_prod Finset.univ fun k _ => hv_zpow hp (hsingle k) (hy k) (hz k) (d k)
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

end HV

section Frame

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L]

theorem isFrameAt_of_tri (V : Lat ξ L) (p : Cpt ξ) {r : ℕ} (b b₀ : Fin r → L) (T : Matrix (Fin r) (Fin r) Ω)
    (hfl : ∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) (hb : V.IsFrameAt b p) (hT : ∀ i, b i = ∑ j, T i j • b₀ j)
    (h1 : ∀ i j, T i j ∈ regAt ξ p) (h2 : ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ regAt ξ p) : V.IsFrameAt b₀ p := by
  obtain ⟨hi, htri⟩ := GlobalTheory.T.flag_equal_change_lower_triangular Ω L r b b₀ T hb.1 hfl hT
  refine ⟨hi, hb.2.trans (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))⟩
  · rintro _ ⟨i, rfl⟩
    rw [hT]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (⟨T i j, h1 i j⟩ : regAt ξ p) (Submodule.subset_span ⟨j, rfl⟩)
  · have key : ∀ n : ℕ, ∀ i : Fin r, (i : ℕ) = n → b₀ i ∈ Submodule.span (regAt ξ p) (Set.range b) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi'
        have e : b₀ i = (T i i)⁻¹ • (b i - ∑ j ∈ Finset.univ.erase i, T i j • b₀ j) := by
          rw [hT i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_right, smul_smul,
            inv_mul_cancel₀ (h2 i).1, one_smul]
        rw [e]
        refine Submodule.smul_mem _ (⟨_, (h2 i).2⟩ : regAt ξ p) (Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
          (Submodule.sum_mem _ fun j hj => ?_))
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
        · exact Submodule.smul_mem _ (⟨T i j, h1 i j⟩ : regAt ξ p) (ih j (hi' ▸ h) j rfl)
        · rw [htri i j h, zero_smul]
          exact Submodule.zero_mem _
    rintro _ ⟨i, rfl⟩
    exact key i i rfl

end Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem interior_of {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y₁ : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y₁) (z : Sp ℂ ⟶ 𝔐.X) (v : Sp ℂ ⟶ Xo.XF c) (hv : v ≫ Y.j = z ≫ 𝔐.f) :
    𝔐.Interior z ∧ HodgeMetric.PolarisedAt 𝔐.t z := by
  constructor
  · have hmem : Y.jQ (v (IsLocalRing.closedPoint ℂ)) ∈
        Limits.pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have e : Limits.pullback.fst Y.s (spMap β) (Y.jQ (v (IsLocalRing.closedPoint ℂ))) = 𝔐.f (GlobalTheory.CompanionTheory.Ar.centre z) := by
      have h2 : (v ≫ Y.jQ ≫ Limits.pullback.fst Y.s (spMap β))
          (IsLocalRing.closedPoint ℂ) = (z ≫ 𝔐.f) (IsLocalRing.closedPoint ℂ) := by
        rw [show v ≫ Y.jQ ≫ Limits.pullback.fst Y.s (spMap β) = z ≫ 𝔐.f from hv]
      simp only [Scheme.Hom.comp_apply] at h2
      exact h2
    have hab : 𝔐.f (GlobalTheory.CompanionTheory.Ar.centre z) ∈ abLocus Y.t.G := e ▸ hmem
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (GlobalTheory.CompanionTheory.Ar.centre z)).1 hab
  · obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
    have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ Limits.pullback.fst _ _) (_ : SABMap t' Y.t q),
        Nonempty (SABMap t' Y.oF.t v) := by
      intro q hq n; subst hq
      exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
    obtain ⟨m₃⟩ := cancel _ hv.symm n
    obtain ⟨w₂, g₂, -⟩ := m₃.lin
    obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
    exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

variable {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

set_option maxHeartbeats 400000 in
theorem pt_frame (Fr : Small.GenFrame Or) (F : Type) [Field F] [Algebra c.F F] (zC : Sp F ⟶ Or.𝔐.X) (q : TRing c.F)
    (φ : letI := Small.cstAlg Or; q.R →ₐ[c.F] RM.Ω) (yq : FrPt Xo c q.R)
    (hφ : letI := Small.cstAlg Or; FrMap φ yq Fr.y₀) (ψ : q.R →ₐ[c.F] F) (y : FrPt Xo c F)
    (hψ : FrMap ψ yq y) (hr : ∀ r, ValAt Or.𝔐.ξ zC (φ r) (ψ r)) :
    zC ≫ Or.𝔐.f = Small.ptY Y y ∧ ∀ s i, ∃ v : epsAt zC ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt zC (Or.Fl.b s i) v ∧
      v.left ≫ Or.𝔐.m.φ = Small.tanY Y y (Small.labelC s) (Small.labelFin Dw s i) := by
  letI := Small.cstAlg Or
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre zC := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨GlobalTheory.CompanionTheory.Ar.centre zC, hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo zC).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h', s', hs, hs'⟩ := hr r
    exact ⟨s', hs, hs'⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  refine ⟨?_, fun s i => ?_⟩
  · have e0 : spMap (Scheme.stalkClosedPointTo zC).hom ≫ Or.𝔐.X.fromSpecStalk P.1 = zC := LieTangent.spec_centre zC
    have e1 : spMap (Scheme.stalkClosedPointTo zC).hom ≫ spMap θ = spMap ψ.toRingHom :=
      (LieTangent.spec_comp _ _).trans (congrArg (fun g => spMap g) hθ2)
    have e2 : Small.ptY Y y = spMap ψ.toRingHom ≫ Small.ptY Y yq := Small.ptY_map Y hψ
    refine (congrArg (· ≫ Or.𝔐.f) e0.symm).trans ((Category.assoc _ _ _).trans ?_)
    exact (congrArg (fun g => _ ≫ g) he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Small.ptY Y yq) e1).trans e2.symm))
  obtain ⟨v, hvt, hv'⟩ := exists_tan_lift Or.𝔐.m.cart (Or.𝔐.X.fromSpecStalk P.1) θ (Small.ptY Y yq)
    (Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) (Small.tanY_hom Y _ _ _) (tanY_one Y _ _ _) he
  have hext : Or.𝔐.M.Extends P (Or.Fl.b s i) v := by
    refine extends_of Or.𝔐.m.cart _ P _ v hvt ?_
    have e2 := Small.tanY_map Y hφ (Small.labelC s) (Small.labelFin Dw s i)
    have e3 := Fr.tan_eq s i
    have e4 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap Or.𝔐.ξ P)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
          Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
      rw [← Category.assoc, spec_dual_comp, hθ1]
    exact e3.symm.trans (e2.trans (e4.trans (congrArg (fun u => _ ≫ u) hv'.symm)))
  obtain ⟨EC, _, _, ⟨MC⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Or.𝔐.X Or.𝔐.t.G F zC
  have hb := LieTangent.isTanAt_base _ (LieTangent.spec_centre zC) hvt
  obtain ⟨w, hw⟩ := MC.onto _ hb
  refine ⟨MC.pt w, (Or.𝔐.M.valAt_iff _ _ _).2 ⟨hgen, v, hext, hw⟩, ?_⟩
  have e5 : (MC.pt w).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ v.left :=
    congrArg (fun u => u.left) hw
  have e6 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
        Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
    have e7 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) := (spec_dual_comp θ _).trans (by rw [hθ2])
    exact (congrArg (fun u => u ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) e7.symm).trans
      (Category.assoc _ _ _)
  have e8 : Small.tanY Y y (Small.labelC s) (Small.labelFin Dw s i) =
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := Small.tanY_map Y hψ _ _
  refine Eq.trans ?_ (e8.trans e6).symm
  rw [e5]
  exact (Category.assoc _ _ _).trans (congrArg (fun u => _ ≫ u) hv')

end PositivityTheory.UnitarySelfGeneration.RA
