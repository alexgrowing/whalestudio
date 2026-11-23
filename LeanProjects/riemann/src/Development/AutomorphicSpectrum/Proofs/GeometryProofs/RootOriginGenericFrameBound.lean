import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartnerPointIntegralModel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FirstFormIffSecondForm
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NaturalOfChartIndep
import Development.WeilBound.CoreStatements.AdicCompleteSpans.MinorC
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {N : Type} [NormedField N]

theorem norm_eq_zpow (j : K →+* N) (hj : ∀ x : V, ‖j (algebraMap V K x)‖ ≤ 1) {π : K} (hπ : vV V π = 1)
    {x : K} (hx : x ≠ 0) : ‖j x‖ = ‖j π‖ ^ vV V x := by
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ
  have hu0 : x * π ^ (-vV V x) ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hv : vV V (x * π ^ (-vV V x)) = 0 := by
    rw [vV_mul hx (zpow_ne_zero _ hπ0), GlobalTheory.ThetaValueIdentityCompare.vV_zpow, hπ]
    ring
  obtain ⟨u, hu, hue⟩ := GlobalTheory.ThetaValueIdentityCompare.exists_unit hu0 hv
  have hn : ‖j (algebraMap V K u)‖ = 1 := by
    obtain ⟨w, rfl⟩ := hu
    have h1 := hj (w : V)
    have h2 := hj ((w⁻¹ : Vˣ) : V)
    have h3 : ‖j (algebraMap V K (w : V))‖ * ‖j (algebraMap V K ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul]
      simp
    nlinarith [norm_nonneg (j (algebraMap V K (w : V))), norm_nonneg (j (algebraMap V K ((w⁻¹ : Vˣ) : V)))]
  rw [hue, map_mul, norm_mul, map_zpow₀, norm_zpow, zpow_neg] at hn
  have hb : ‖j π‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hπ0)
  field_simp at hn
  exact hn

end Val

section Loc

open scoped NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]

theorem zpow_eq_rpow {b : ℝ} (hb : 0 < b) {n m : ℤ} (h : b ^ n = (p : ℝ)⁻¹) :
    b ^ m = (p : ℝ) ^ (-((m : ℝ) / (n : ℝ))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : n ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at h
    have := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hl := congrArg Real.log h
  rw [Real.log_zpow, Real.log_inv] at hl
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (zpow_pos hb m), Real.log_zpow]
  congr 1
  field_simp
  linear_combination (m : ℝ) * hl

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem unitBall : GlobalTheory.BK.IsUnitBall 𝒪[L] L where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ Valued.integer.mem_iff.1 y.2, fun h => ⟨⟨x, Valued.integer.mem_iff.2 h⟩, rfl⟩⟩

attribute [local instance] unitBall

theorem dvr_fin [FiniteDimensional ℚ_[p] L] : IsDiscreteValuationRing 𝒪[L] ∧ Finite 𝓀[L] := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : CompactSpace 𝒪[L] := by
    have : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [Valued.integer.mem_iff]
    exact isCompact_iff_compactSpace.1 (this ▸ isCompact_closedBall 0 1)
  have : (Valued.v : Valuation L NNReal).RankOne := inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := L)))
  obtain ⟨-, h1, h2⟩ :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.1 hc
  exact ⟨h1, h2⟩

theorem exists_cdvr [FiniteDimensional ℚ_[p] L] :
    ∃ (T : CDVR) (j : T.Fr →+* PadicAlgCl p), T.FinRes ∧ ((p : ℕ) : T.V) ∈ IsLocalRing.maximalIdeal T.V ∧
      (∀ x ∈ L, x ∈ Set.range j) ∧
      ∀ x : T.Fr, x ≠ 0 → ‖j x‖ = (p : ℝ) ^ (-((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ))) := by
  obtain ⟨hd, hf⟩ := dvr_fin L
  have : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[L]) 𝒪[L] :=
    PositivityTheory.CompleteLocalMinorRing.Minor.isAdicComplete_max (K := L) p
  have h0 : CharZero 𝒪[L] := ⟨fun a b h => Nat.cast_injective (R := L) (by
    have := congrArg (algebraMap 𝒪[L] L) h
    simpa using this)⟩
  let T : CDVR := { V := 𝒪[L], dvr := hd, cpl := hc, ch0 := h0 }
  let e : T.Fr ≃+* L := (FractionRing.algEquiv 𝒪[L] L).toRingEquiv
  let j : T.Fr →+* PadicAlgCl p := (algebraMap L (PadicAlgCl p)).comp e.toRingHom
  have hje : ∀ x : T.Fr, j x = ((e x : L) : PadicAlgCl p) := fun _ => rfl
  have hea : ∀ x : 𝒪[L], e (algebraMap 𝒪[L] T.Fr x) = (x : L) := fun x =>
    (FractionRing.algEquiv 𝒪[L] L).commutes x
  have hj : ∀ x : T.V, ‖j (algebraMap T.V T.Fr x)‖ ≤ 1 := fun x => by
    rw [hje]
    erw [hea x]
    exact Valued.integer.norm_le_one x
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_exists_uniformizer T.Fr
  have hπ1 : vV T.V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have hb : 0 < ‖j π‖ := norm_pos_iff.2 ((map_ne_zero j).2 hπ0)
  have hp0 : ((p : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpn : ‖j π‖ ^ vV T.V ((p : ℕ) : T.Fr) = (p : ℝ)⁻¹ := by
    rw [← norm_eq_zpow j hj hπ1 hp0, map_natCast, norm_natCast_p]
  refine ⟨T, j, hf, ?_, fun x hx => ⟨e.symm ⟨x, hx⟩, ?_⟩, fun x hx => ?_⟩
  · refine (PositivityTheory.CompleteLocalMinorRing.Minor.mem_max_iff (K := L)).2 ?_
    rw [map_natCast]
    have : ‖((p : ℕ) : L)‖ = ‖((p : ℕ) : PadicAlgCl p)‖ := rfl
    rw [this, norm_natCast_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  · rw [hje, e.apply_symm_apply]
  · rw [norm_eq_zpow j hj hπ1 hx]
    exact zpow_eq_rpow hb hpn

end Loc

section Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem aeval_mem {σ : Type} {z : σ → PadicAlgCl p} {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L)
    (g : MvPolynomial σ ℤ) : MvPolynomial.aeval z g ∈ L := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    simp [intCast_mem L a]
  | add f g hf hg =>
    rw [map_add]
    exact L.add_mem hf hg
  | mul_X f i hf =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact L.mul_mem hf (hz i)

theorem hasVal_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → PadicAlgCl p} {w : PadicAlgCl p}
    {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L) (h : Small.HasVal y a s z w) : w ∈ L := by
  obtain ⟨dg, dh, g, f, -, -, -, -, h0, e⟩ := h
  rw [eq_div_of_mul_eq h0 e.symm]
  exact L.div_mem (aeval_mem hz g) (aeval_mem hz f)

theorem finite_adjoin {σ : Type} [Finite σ] (z : σ → PadicAlgCl p) :
    FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range z)) := by
  have : Finite (Set.range z) := Set.finite_range z |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem vLa_p {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} (hla : (p : 𝓞 F) ∈ la.asIdeal) :
    vLa la ((p : ℕ) : F) = ramOverZ la := by
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  have := Formalism.L2.Pj.Crude.crv_vLa_char la
  rw [hres] at this
  exact this

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

theorem exists_isIntPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), IntAll Xo c → Ref.UnifAll Xo c → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∃ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr hInt hUnif A p _ z ev hz hv hG
  obtain ⟨hc1, hc2, -, -⟩ := hG
  have hzL : ∀ i, z i ∈ IntermediateField.adjoin ℚ_[p] (Set.range z) := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have := Pt.finite_adjoin z
  obtain ⟨T₀, j, hfin, hpm, hL, hnorm⟩ := Pt.exists_cdvr (IntermediateField.adjoin ℚ_[p] (Set.range z))
  have hev : ∀ x : A, ∃ a, j a = ev x := fun x => hL _ (Pt.hasVal_mem hzL (hv x))
  choose f hf using hev
  have hinj : Function.Injective j := j.injective
  let ev₀ : A →+* T₀.Fr :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hf, map_add, map_add, hf, hf]) }
  have hev₀ : ∀ x, j (ev₀ x) = ev x := hf
  let cA : c.F →+* A := Or.𝔐.cst.codRestrict A hc1
  let io₀ : c.F →+* T₀.Fr := ev₀.comp cA
  obtain ⟨la, e₀, ho₀, hpla⟩ := GlobalTheory.PartnerIn.exists_overLa T₀ io₀ (Fact.out : p.Prime) hpm
  obtain ⟨q, φq, yq, hyq, hφA⟩ := hc2
  letI a0 : Algebra c.F T₀.Fr := io₀.toAlgebra
  letI aΩ : Algebra c.F RM.Ω := Small.cstAlg Or
  let ψ₀ : q.R →ₐ[c.F] T₀.Fr :=
    { ev₀.comp (φq.toRingHom.codRestrict A hφA) with
      commutes' := fun a => by
        show ev₀ _ = ev₀ (cA a)
        exact congrArg ev₀ (Subtype.ext (φq.commutes a)) }
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c q.R yq T₀.Fr ψ₀
  obtain ⟨T', io', e', y', ho', hy', φ, z₁, t, -, hφy, hb⟩ := hInt la T₀ io₀ e₀ ho₀ hfin y₁
  obtain ⟨T, φV, φ₂, r, yy, τ, hfe, hbc, hyA, hτ⟩ := hUnif la T' io' e' ho' y' hy'
  letI a1 : Algebra c.F T'.Fr := io'.toAlgebra
  letI a2 : Algebra c.F T.Fr := (φ₂.comp io').toAlgebra
  let φ₂A : T'.Fr →ₐ[c.F] T.Fr := { φ₂ with commutes' := fun _ => rfl }
  obtain ⟨zT, hzT⟩ := GlobalTheory.ThetaExprBaseChangeTest.frBCField Xo c T'.Fr z₁ T.Fr φ₂A
  have hFB := frBorBC T'.Fr T.Fr φ₂A t z₁ y'.1 zT yy.1 hb hzT hbc
  refine ⟨la, T, φ₂.comp io', r * e', yy, (φ₂.comp φ.toRingHom).comp ev₀, zT,
    fun i => Units.map (φ₂A : T'.Fr →* T.Fr) (t i), ?_⟩
  unfold FinRd.IsIntPt
  refine ⟨hpla, hfe.overLa ho', hyA, ⟨τ, hτ⟩, fun a h => ?_, fun x => ?_,
    ⟨q, φq, φ₂A.comp (φ.comp ψ₀), yq, hyq, ?_, fun r => ⟨hφA r, rfl⟩⟩, hFB⟩
  · show φ₂ (φ (ev₀ ⟨_, h⟩)) = φ₂ (io' a)
    have h1 : φ (io₀ a) = io' a := φ.commutes a
    rw [← h1]
    rfl
  · have hio : φ.toRingHom.comp io₀ = io' := RingHom.ext fun a => φ.commutes a
    have ho'' : OverLa la T'.V (φ.toRingHom.comp io₀) e' := by
      rw [hio]
      exact ho'
    obtain ⟨r', ⟨hr'0, hr'⟩, he'⟩ :=
      (GlobalTheory.ThetaValueIdentityCompare.overLa_iff ho₀ hfin φ.toRingHom e').1 ho''
    have hr0 := hfe.2.2.2.2.1
    have hram := FinRd.ram_pos hpla
    by_cases hx : ev₀ x = 0
    · have h1 : ev x = 0 := by rw [← hev₀ x, hx, map_zero]
      have h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x = 0 := by
        show φ₂ (φ (ev₀ x)) = 0
        rw [hx, map_zero, map_zero]
      rw [h1, norm_zero]
      unfold FinRd.absT
      rw [if_pos h2]
    · have h2 : ((φ₂.comp φ.toRingHom).comp ev₀) x ≠ 0 := by
        show φ₂ (φ (ev₀ x)) ≠ 0
        exact (map_ne_zero φ₂).2 ((map_ne_zero φ).2 hx)
      rw [← hev₀ x, hnorm _ hx]
      unfold FinRd.absT
      rw [if_neg h2]
      have hv1 : vV T.V (((φ₂.comp φ.toRingHom).comp ev₀) x) = r * (r' * vV T₀.V (ev₀ x)) := by
        show vV T.V (φ₂ (φ (ev₀ x))) = _
        rw [hfe.2.2.2.2.2]
        congr 1
        exact hr' _ hx
      have hv2 : vV T₀.V ((p : ℕ) : T₀.Fr) = e₀ * ramOverZ la := by
        have h3 := ho₀.2 ((p : ℕ) : c.F)
        rw [map_natCast, Pt.vLa_p hpla] at h3
        exact h3
      have he0 : (e₀ : ℝ) ≠ 0 := by exact_mod_cast ho₀.1.ne'
      have hr1 : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
      have hr2 : (r' : ℝ) ≠ 0 := by exact_mod_cast hr'0.ne'
      have hr3 : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hram.ne'
      rw [hv1, hv2, he']
      push_cast
      congr 2
      field_simp
  · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hy₁ hφy) hzT

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
