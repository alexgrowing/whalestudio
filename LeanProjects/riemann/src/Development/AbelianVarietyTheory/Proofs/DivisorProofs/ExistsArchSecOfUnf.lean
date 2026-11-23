import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulIdemOfBdd
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

open GlobalTheory.DetLine GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal in

theorem exists_horizontal (hp : GlobalTheory.CovTop.Hypotheses2) (hpos : 1 ≤ Dw.p + Dw.q) (hgeo : FnAlgClosed Xo c) (Z : Comp Xo c)
    (τ : Psi H) : ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1),
      (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧
        GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hpos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hgeo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm

theorem framesOn_eq {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed Xo c) (Z : Comp Xo c) : ∃ k, framesOn U Z = {z | z.1 = k ∧ z.2 ∈ (U.X z.1).dom} := by
  obtain ⟨q, hq⟩ : ∃ q : U.Comp ≃ Comp Xo c, ∀ k (y : (U.X k).dom) (s : Sp (CAt σ)),
      GlobalTheory.AllWt.ptF (U.un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hgeo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this

open GlobalTheory.BdryUnit in

theorem const_length {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed Xo c) {Z : Comp Xo c} {τ : Psi H} {Y : Model Xo c (RingHom.id c.F)} {V : (Xo.XF c).Opens}
    {sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1} {f : Rul Xo c} (hV : (V : Set (Xo.XF c)) = Z)
    (hn : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig) (hh : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig) (hr : Reads Y V τ sig f) :
    ∃ b : ℝ, 0 < b ∧ homN U x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn U Z = {b} := by
  obtain ⟨k, hk⟩ := framesOn_eq U hσ hU hgeo Z
  have hτ : relab c σ τ.1 ∈ (U.X k).Ψ := by
    refine ((hU.2.1 k).2 _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0
  obtain ⟨a, ha⟩ := rdU_eq_mul_horizGen U hσ hU τ hn hh hr k hτ
  obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty (U.X k)
  have hy' : (⟨k, y⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z := by rw [hk]; exact ⟨rfl, hy⟩
  have ha0 : a ≠ 0 := by
    obtain ⟨h1, h2⟩ := ha ⟨y, hy⟩ (hV ▸ hy'.2)
    exact left_ne_zero_of_mul (h2 ▸ h1)
  refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 (U.X k).Gm.det‖),
    mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha0) (Real.sqrt_pos.2 (norm_pos_iff.2
      ((map_ne_zero _).2 (U.X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨_, hy'⟩, ?_⟩⟩
  rintro ⟨k', y'⟩ hz
  have hz' := hz
  rw [hk] at hz'
  obtain ⟨rfl, hy₁⟩ : k' = k ∧ y' ∈ (U.X k').dom := hz'
  have h1 := (ha ⟨y', hy₁⟩ (hV ▸ hz.2)).2
  rw [← pnorm_horizGen (U.X k') ⟨_, hτ⟩ hy₁, homN, ptN, modelWt_flatWt U hσ hU τ k' hτ]
  simp only at h1
  simp only [Data.pnorm, h1, norm_mul, mul_assoc]

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}

theorem evR_sig_mul_inv (s : ArchSec U x Z (flatWt Dw τ)) {k : Type} [Field k] [Algebra c.F k] {y : FrPt Xo c k}
    (h : LiesOn Z y) : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
  rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem h (GlobalTheory.FlagTan.fromTest_of_isLocalRing y)]

theorem detLaw_sig (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.sig τ.1 (conjEmb τ.1) :=
  ⟨s.sig_mem.1, fun _ _ _ z y _ h g₁ g₂ h₁ h₂ => GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₁ g₂ h₁ h₂⟩

theorem detLaw_inv (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.inv (conjEmb τ.1) τ.1 := by
  refine ⟨s.inv_mem.1, fun k _ _ z y hy h g₁ g₂ h₁ h₂ => ?_⟩
  have hz : LiesOn Z z := by
    have e : GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF y := by
      apply pullback.hom_ext
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, h]
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]
    exact fun p => e ▸ hy p
  have k1 := GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₂ g₁ h₂ h₁
  have k2 := evR_sig_mul_inv s hy
  have k3 := evR_sig_mul_inv s hz
  linear_combination (-(evR Xo c s.inv z * evR Xo c s.inv y)) * k1 + (g₂.det * evR Xo c s.inv y) * k3 -
    (g₁.det * evR Xo c s.inv z) * k2

set_option synthInstance.maxHeartbeats 400000 in

theorem archSec_denom (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (s : ArchSec U x Z (flatWt Dw τ))
    (hs : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  have hb : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) →
      evI y₀ s.sig ∈ (algebraMap T.V T.Fr).range ∧ evI y₀ s.inv ∈ (algebraMap T.V T.Fr).range := by
    intro T io y₀ h1 h2
    letI := io.toAlgebra
    have h3 := hs T io y₀ h1 h2
    have h4 : evI y₀ s.sig * evI y₀ s.inv = 1 := evR_sig_mul_inv s h2
    have h5 := left_ne_zero_of_mul_eq_one h4
    have h6 := right_ne_zero_of_mul_eq_one h4
    rw [nval_of_ne h5, EReal.coe_eq_zero, Nat.cast_one, div_one, Int.cast_eq_zero] at h3
    have h7 := vV_mul (V := T.V) h5 h6
    rw [h4, show vV T.V (1 : T.Fr) = 0 by simp [vV], h3] at h7
    exact ⟨Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) h3.ge,
      Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) (by omega)⟩
  obtain ⟨m₁, hm₁, h₁⟩ := Cover.exists_denom hpq hA Z (detLaw_sig s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).1
  obtain ⟨m₂, hm₂, h₂⟩ := Cover.exists_denom hpq hA Z (detLaw_inv s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).2
  have hn : ∀ (n : ℕ), 0 < n → ∀ la, ∀ v ∈ valOn Z la, ∀ f : Rul Xo c, 0 ≤ v f → 0 ≤ v ((n : c.F) • f) := by
    intro n hn la v hv f hf
    rw [(isVal_valOn hv).smul _ _ (Nat.cast_ne_zero.2 hn.ne')]
    refine add_nonneg (EReal.coe_nonneg.2 ?_) hf
    have := Formalism.L2.Pj.vAdd_int_nonneg la (a := (n : 𝓞 c.F)) (by
      have : (n : c.F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      simpa using this)
    have h2 : 0 ≤ Formalism.BasicNotions.vAdd la (n : c.F) := by simpa using this
    exact_mod_cast h2
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun la v hv => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact hn _ hm₂ la v hv _ (h₁ la v hv)
  · rw [Nat.cast_mul, mul_smul]
    exact hn _ hm₁ la v hv _ (h₂ la v hv)

theorem exists_archSec_of_unf (hP : GlobalTheory.CovTop.Hypotheses2) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hgeo : FnAlgClosed Xo c) (x : ℝ) (Z : Comp Xo c) (τ : Psi H) :
    ∃ (s : ArchSec U x Z (flatWt Dw τ)) (m : ℕ), 0 < m ∧
      ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := exists_horizontal hP hpq hgeo Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.BdryUnit.ReadDet.exists_reads E H Dw l Xo c Y Z V τ sig hV hs hnv
  choose b hb hb' using fun σ => const_length (U _) x (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) hgeo hV hnv hh hR
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, archSec_denom hpq hA _ fun T io y₀ h0 hZ =>
    GlobalTheory.BdryUnitVal.unit_at_integral hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩

end GlobalTheory.FlatDenom

open Formalism.BasicNotions GlobalTheory.CovTop in

theorem GlobalTheory.FlatDenom.exists_archSec_denom : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ (s : GlobalTheory.FlatCore.ArchSec Y.U (xiR D) Z (GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ)) (m : ℕ), 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s.sig) ∧ 0 ≤ v ((m : Y.d.c₂.F) • s.inv) := by
  intro hP D T j Y e o hG _ Z τ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have h1 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
  exact GlobalTheory.FlatDenom.exists_archSec_of_unf hP (by omega) hG.lev.2 hG.unf hG.geo _ Z τ

namespace GlobalTheory.FlatDenom

section Powers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def HasBddSec (la : GlobalTheory.AllWt.Weight Dw) : Prop :=
  ∃ (s : ArchSec U x Z la) (m : ℕ), 0 < m ∧ ∀ w, ∀ v ∈ valOn Z w, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv)

variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}

theorem homN_sig (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw la 0) s.sig z = s.cInf σ := (image_eq_singleton_iff.1 (s.norm_inf σ)).2 z hz

theorem homN_inv (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw (-la) 0) s.inv z = (s.cInf σ)⁻¹ := by
  have h := homN_mul (U (goodOf c σ)) x (even_wtOf (-la) 0) (even_wtOf la 0) s.inv s.sig z hz.1
  rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm s.inv, s.mul_inv, homN_sig s hz,
    homN_idem _ x hz.1 hz.2 (tested_of_homN_ne _ x hz.1 ((homN_sig s hz).symm ▸ (s.cInf_pos σ).ne'))] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem HasBddSec.neg (h : HasBddSec U x Z la) : HasBddSec U x Z (-la) := by
  obtain ⟨s, m, hm, h⟩ := h
  exact ⟨⟨s.inv, s.sig, exOf_neg la ▸ s.inv_mem, by rw [exOf_neg, neg_neg]; exact s.sig_mem, s.idem_inv, s.idem_sig,
    by rw [mul_comm, s.mul_inv], s.cInf⁻¹, fun σ => inv_pos.2 (s.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => homN_inv s hz⟩⟩, m, hm,
    fun w v hv => (h w v hv).symm⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem HasBddSec.add (h : HasBddSec U x Z la) (h' : HasBddSec U x Z la') : HasBddSec U x Z (la + la') := by
  obtain ⟨s, m, hm, h⟩ := h
  obtain ⟨t, m', hm', h'⟩ := h'
  refine ⟨⟨s.sig * t.sig, s.inv * t.inv, exOf_add' la la' ▸ mul_mem_secZ s.sig_mem t.sig_mem,
    by rw [exOf_add', neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem, by rw [← mul_assoc, s.idem_sig],
    by rw [← mul_assoc, s.idem_inv], by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem],
    s.cInf * t.cInf, fun σ => mul_pos (s.cInf_pos σ) (t.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => ?_⟩⟩, m * m', Nat.mul_pos hm hm', fun w v hv => ?_⟩
  · rw [wtOf_add', homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) _ _ _ hz.1, homN_sig s hz, homN_sig t hz]; rfl
  · have hV := isVal_valOn hv
    constructor
    · show 0 ≤ v (_ • (s.sig * t.sig))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).1 (h' w v hv).1
    · show 0 ≤ v (_ • (s.inv * t.inv))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).2 (h' w v hv).2

theorem HasBddSec.zsmul (h : HasBddSec U x Z la) (n : ℤ) : HasBddSec U x Z (n • la) := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul, ← add_neg_cancel la]; exact h.add h.neg
  | succ n ih => rw [add_smul, one_smul]; exact ih.add h
  | pred n ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact ih.add h.neg

end Powers

theorem exists_nat_vAdd {K : Type} [Field K] [NumberField K] {a : K} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ Formalism.BasicNotions.vAdd w ((n : K) * a) := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_integral_multiple
  have hn : IsIntegral ℤ ((y.natAbs : K) * a) := by
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with e | e
    · rw [e, Int.cast_natCast] at hy; exact hy
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at hy; simpa using hy.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun w => ?_⟩
  exact Formalism.L2.Pj.vAdd_int_nonneg w (a := (⟨_, hn⟩ : 𝓞 K))
    (mul_ne_zero (Nat.cast_ne_zero.2 (Int.natAbs_pos.2 hy0).ne') ha)

end GlobalTheory.FlatDenom

open Formalism.BasicNotions GlobalTheory.CovTop in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FlatDenom.unit_pow_denom : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  intro hP D T j Y e o hY hE n Z τ s i ⟨hs, hi, hIs, hIi, hsi, hb⟩
  have h₁ : HasBddSec Y.U (xiR D) Z (flatWt (T.Q.Dw j) τ) := exists_archSec_denom hP D T j Y e o hY hE Z τ
  obtain ⟨s₀, m₀, hm₀, h₀⟩ := h₁.zsmul n
  generalize n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ = la at *
  have hw : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) (-la) 0 = 0 := by
    rw [← GlobalTheory.FlatLine.wtOf_add', add_neg_cancel, GlobalTheory.AllWt.wtOf_zero]
  have hg : s * s₀.inv ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hs s₀.inv_mem
    have h0 : Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + -GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      add_neg_cancel _
    rwa [h0] at h
  have hh : i * s₀.sig ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hi s₀.sig_mem
    have h0 : -Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      neg_add_cancel _
    rwa [h0] at h
  have hIg : GlobalTheory.FlatLine.idem Z * (s * s₀.inv) = s * s₀.inv := by rw [← mul_assoc, hIs]
  have hIh : GlobalTheory.FlatLine.idem Z * (i * s₀.sig) = i * s₀.sig := by rw [← mul_assoc, hIi]
  have hgh : s * s₀.inv * (i * s₀.sig) = GlobalTheory.FlatLine.idem Z := by
    calc s * s₀.inv * (i * s₀.sig) = (s * i) * (s₀.sig * s₀.inv) := by ring
      _ = _ := by rw [hsi, s₀.mul_inv, GlobalTheory.FlatLine.idem_mul_idem]
  have hbd : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z,
      GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (s * s₀.inv) z ≤ C ∧
        GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (i * s₀.sig) z ≤ C := by
    intro σ hσ
    obtain ⟨C, hC⟩ := hb σ hσ
    have hgo : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ := if_pos hσ
    have hN : ∀ σ'' (_ : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ''), ∀ z ∈ framesOn (Y.U σ'') Z,
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) la 0) s₀.sig z = s₀.cInf σ ∧
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) (-la) 0) s₀.inv z = (s₀.cInf σ)⁻¹ := by
      rintro _ rfl z hz
      exact ⟨homN_sig s₀ hz, homN_inv s₀ hz⟩
    have hpos := s₀.cInf_pos σ
    refine ⟨max (C * (s₀.cInf σ)⁻¹) (C * s₀.cInf σ), fun z hz => ?_⟩
    have hd : z.2 ∈ ((Y.U σ).X z.1).dom := hz.1
    obtain ⟨h1, h2⟩ := hN σ hgo z hz
    obtain ⟨c1, c2⟩ := hC z hz
    have hev : Even (-(wtOf (T.Q.Dw j) la 0)).2 := by
      simpa using (GlobalTheory.AllWt.even_wtOf (Dw := T.Q.Dw j) la 0).neg
    have e1 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) (GlobalTheory.AllWt.even_wtOf la 0) (GlobalTheory.AllWt.even_wtOf (-la) 0)
      s s₀.inv z hd
    rw [hw, h2] at e1
    have e2 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) hev (GlobalTheory.AllWt.even_wtOf la 0) i s₀.sig z hd
    rw [neg_add_cancel, h1] at e2
    constructor
    · rw [e1]; exact (mul_le_mul_of_nonneg_right c1 (inv_pos.2 hpos).le).trans (le_max_left _ _)
    · rw [e2]; exact (mul_le_mul_of_nonneg_right c2 hpos.le).trans (le_max_right _ _)
  obtain ⟨a, ha⟩ := GlobalTheory.CovTop.koecher_unit_const hP D T j Y e o hY hE Z _ _ hg hh hIg hIh hgh hbd
  have hsa : s = a • s₀.sig := by
    calc s = s * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIs]
      _ = (s * s₀.inv) * s₀.sig := by rw [← s₀.mul_inv]; ring
      _ = a • s₀.sig := by rw [ha, smul_mul_assoc, s₀.idem_sig]
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun w v hv => ?_⟩
    exfalso
    have h1 := GlobalTheory.FlatLine.val_idem hv
    rw [← hsi, hsa, ha0, zero_smul, zero_mul, (GlobalTheory.FlatLine.isVal_valOn hv).zero] at h1
    exact EReal.top_ne_zero h1
  have hia : i = a⁻¹ • s₀.inv := by
    calc i = i * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIi]
      _ = i * (a • s₀.sig * a⁻¹ • s₀.inv) := by rw [GlobalTheory.FlatLine.smul_mul_inv_smul ha0, s₀.mul_inv]
      _ = (s * i) * a⁻¹ • s₀.inv := by rw [← hsa]; ring
      _ = a⁻¹ • s₀.inv := by rw [hsi, mul_smul_comm, s₀.idem_inv]
  obtain ⟨n₁, hn₁, k₁⟩ := exists_nat_vAdd ha0
  obtain ⟨n₂, hn₂, k₂⟩ := exists_nat_vAdd (inv_ne_zero ha0)
  have hnat : ∀ (k : ℕ), 0 < k → ∀ w, 0 ≤ vAdd w (k : Y.d.c₂.F) := fun k hk w => by
    have := Formalism.L2.Pj.vAdd_int_nonneg w (a := (k : 𝓞 Y.d.c₂.F)) (by
      have : (k : Y.d.c₂.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simpa using this)
    simpa using this
  have key : ∀ (b : Y.d.c₂.F) (k k' : ℕ) (f : Rul Y.d.Xo₂ Y.d.c₂), b ≠ 0 → 0 < k → 0 < k' → ∀ w, ∀ v ∈ valOn Z w,
      0 ≤ vAdd w ((k : Y.d.c₂.F) * b) → 0 ≤ v ((m₀ : Y.d.c₂.F) • f) →
      0 ≤ v (((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f) := fun b k k' f hb hk hk' w v hv h1 h2 => by
    have hV := GlobalTheory.FlatLine.isVal_valOn hv
    have e1 : ((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f = (k' : Y.d.c₂.F) • ((k : Y.d.c₂.F) * b) • (m₀ : Y.d.c₂.F) • f := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e1, hV.smul _ _ (Nat.cast_ne_zero.2 hk'.ne'), hV.smul _ _ (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') hb)]
    exact add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast hnat k' hk' w))
      (add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast h1)) h2)
  refine ⟨n₂ * n₁ * m₀, Nat.mul_pos (Nat.mul_pos hn₂ hn₁) hm₀, fun w v hv => ⟨?_, ?_⟩⟩
  · rw [hsa]
    exact key a n₁ n₂ _ ha0 hn₁ hn₂ w v hv (k₁ w) (h₀ w v hv).1
  · rw [hia, mul_comm n₂]
    exact key a⁻¹ n₂ n₁ _ (inv_ne_zero ha0) hn₂ hn₁ w v hv (k₂ w) (h₀ w v hv).2

end
