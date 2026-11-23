import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVectorStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc IsLocalRing

namespace GlobalTheory.UPoinc.USum

section Cong
variable {Y : Type} [AddCommGroup Y]

theorem cm_trans {N : ℕ} {x y z : Y} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_symm {N : ℕ} {x y : Y} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_map {Y' : Type} [AddCommGroup Y'] (f : Y →+ Y') {N : ℕ} {x y : Y} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add, map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : Y} (h : (QuotientAddGroup.mk x : ModN N Y) = QuotientAddGroup.mk y) : CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : Y} (h : CongMod N x y) : (QuotientAddGroup.mk x : ModN N Y) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

end Cong

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {p : ℕ}
  [Fact p.Prime] {Y : Type} [AddCommGroup Y] {q : Y → ℝ}

variable (ρ M q) in

def GLab (y : Sp (PadicAlgCl p) ⟶ M.Z) (yy : S.Gam →+ ModN (S.r * S.N) Y) : Prop :=
  ∃ (c₀ : Ω) (hc : c₀ ≠ 0) (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * S.th x ∈ R') (hev : ∀ x k, c₀ * S.ev x k ∈ R') (ρ' : (S.rechart c₀ hc R' fg frac hth hev).Real),
    USame ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = ρ.i₀ ∧ R' ≤ M.O (y (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = M.val y a) ∧
      ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ Y), (∀ χ, lb.q χ = q (j χ)) ∧
        ∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)

theorem same_of_uSame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : USame ρ ρ' lab φ) : Same ρ (fun _ => 𝟙 _) ρ' (fun _ => 𝟙 _) lab φ := by
  obtain ⟨P₀, a, a', h₁, h₂, l₁, l₂, hp⟩ := h
  exact ⟨P₀, a, a', fun _ => 𝟙 _, h₁, h₂, l₁, l₂, fun _ => ⟨by simp, by simp⟩, hp⟩

theorem GLab.conj [IsNoetherianRing o] (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {σ : Ω →+* Ω} {g : S.Gam → S.Gam}
    (hg : IsConj ρ σ g) {s : M.Z ⟶ M.Z} (hs : M.pt ≫ s = spMap σ ≫ M.pt) {y : Sp (PadicAlgCl p) ⟶ M.Z}
    {yy yy' : S.Gam →+ ModN (S.r * S.N) Y} (h₁ : GLab ρ M q y yy) (h₂ : GLab ρ M q (y ≫ s) yy') :
    ∃ κ : Y ≃+ Y, (∀ x, q (κ x) = q x) ∧ ∀ b ν, yy (g b) = QuotientAddGroup.mk ν → yy' b = QuotientAddGroup.mk (κ ν) := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', hS, -, hR, y₀, hy₀, u, lb, j, hq, hyy⟩ := h₁
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', hS₁, -, hR₁, y₁, hy₁, u', lb', j', hq', hyy'⟩ := h₂
  obtain ⟨P, b, t, hb, ht, l₁, lt, hp⟩ := hg
  obtain ⟨Q, b', b'', hb', hb'', l', l'', hpQ, -⟩ := GalTrans.exists_generic ρ _ ρ' _ ρ'' _ _ _ (same_of_uSame hS)
    (same_of_uSame hS₁) σ g P b t (fun _ => 𝟙 _) hb ht l₁ lt (fun _ => ⟨by simp, by simp⟩) hp
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, -⟩ := GalTrans.spread M hM ρ' ρ'' σ s hs y hR hR₁ y₀ y₁ hy₀ hy₁ u u' Q
    hb' hb'' l' l''
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) := (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ S.r * S.N := NeZero.one_le
  refine ⟨(j.symm.trans e).trans j', fun v => ?_, fun k ν hν => ?_⟩
  · obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← hq, ← hq']
    exact (neg_injective (Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) ((hψ χ _).1 (lb.q_eq χ))
      (lb'.q_eq (e χ))))).symm
  · obtain ⟨w₀, hw₀, e', e''⟩ := hpQ k
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab _ _ w₀ hw₀ e' e''
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ hrN
    obtain ⟨f', hf1', hf2', -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) _ hrN
    obtain ⟨pk, hpk⟩ := hf2 x (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ x hx)
    obtain ⟨pk', hpk'⟩ := hf2' x' (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u' _ x' hx')
    have Q₁ := (hf1 pk x).2 hpk.symm
    have Q₂ := (hf1' pk' x').2 hpk'.symm
    rw [hyy' k _ (lb'.yy_eq _ pk' x' Q₂ hx')]
    have c₀ : CongMod (S.r * S.N) (j.symm ν) pk.y := by
      simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk (hν.symm.trans (hyy _ _ (lb.yy_eq _ pk x Q₁ hx))))
    exact cm_mk (cm_map j'.toAddMonoidHom (cm_trans (htor _ pk pk' x x' w hrN Q₁ Q₂ hw hwa hwa')
      (cm_symm (cm_map e.toAddMonoidHom c₀))))

theorem GLab.tendsto {y : Sp (PadicAlgCl p) ⟶ M.Z} {yy : S.Gam →+ ModN (S.r * S.N) Y} (h : GLab ρ M q y yy) :
    Filter.Tendsto q Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, -, -, y₀, -, u, lb, j, hq, -⟩ := h
  have := lb.pos.comp j.symm.injective.tendsto_cofinite
  refine this.congr fun x => ?_
  simp [hq]

theorem GLab.exists_div [ArithBase o Ω] (hd : M.HasDiv S.th) {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hz : y (cPt p) = z)
    {yy : S.Gam →+ ModN (S.r * S.N) Y} (h : GLab ρ M q (gPt p ≫ y) yy) (hq0 : ∀ x, 0 ≤ q x) {k : ℕ} (hk : 2 ≤ k)
    (hkd : k ∣ S.r * S.N) : ∃ a : S.Gam, k • a = 0 ∧ M.Div S.th a z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, -, hle, y₀, hy₀, u, l, j, hq, -⟩ := h
  have hint : ∀ a : o, ‖y₀ (algebraMap o R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hz ((M.O z).algebraMap_mem a)
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    refine hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg ?_ (by positivity)))))
    rw [hq]
    exact hq0 _
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hkd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, ?_⟩
  obtain ⟨d, hdv⟩ := hd z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hz (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hz
  have e : ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ = ‖y₀ ⟨c₀ * S.th d, hth d⟩‖ * ‖M.val (gPt p ≫ y) (S.th a / S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul (z := (gPt p ≫ y) (closedPoint (PadicAlgCl p)))
      (fun w => by rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]) (hle (hth d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have hn' : ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ = sc := hn
  have b₁ := RatModel.norm_val_le_one hz (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (M.val (gPt p ≫ y) (S.th a / S.th d)))
  nlinarith

theorem GLab.norms [ArithBase o Ω] (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {y : Sp (OO p) ⟶ M.Z} {z : M.Z}
    (hz : y (cPt p) = z) {d : S.Gam} (hd : M.Div S.th d z) {yy : S.Gam →+ ModN (S.r * S.N) Y}
    (h : GLab ρ M q (gPt p ≫ y) yy) {m : ℕ} (hm : S.N = m ^ 2) {a : S.Gam} {ν : Y} (ha : yy a = QuotientAddGroup.mk ν) :
    ((∀ χ, CongMod m χ ν → q ν ≤ q χ) → ∀ h ∈ yy.ker, ∀ (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
      ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ ≤ Real.exp (-q ν)) ∧
    ((∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∀ k, 2 ≤ k → k ∣ m → ∃ h ∈ yy.ker, k • m • h = 0 ∧
      ∀ (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
        ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ = Real.exp (-q ν)) := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hi, hle, y₀, hy₀, u, l, j, hq, hyy⟩ := h
  obtain ⟨ν, rfl⟩ := j.surjective ν
  have hker : yy.ker = l.yy.ker := by
    ext b
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy b χ hχ.symm, ← hχ]
    exact ⟨fun h => cm_mk (by simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk (y := 0) h)),
      fun h => cm_mk (y := 0) (by simpa using cm_map j.toAddMonoidHom (cm_of_mk (y := 0) h))⟩
  have hla : l.yy a = QuotientAddGroup.mk ν := by
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hχ]
    exact cm_mk (by simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk ((hyy a χ hχ.symm).symm.trans ha)))
  have hwt : l.wt (m • ν) = wtChar S (S.perp l.yy.ker) (m • a) :=
    AddMonoidHom.ext (l.wt_eq (m • a) _ (by rw [map_nsmul, hla]; rfl))
  have hint : ∀ a : o, ‖y₀ (algebraMap o R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hz ((M.O z).algebraMap_mem a)
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  set z₀ := (gPt p ≫ y) (closedPoint (PadicAlgCl p))
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : z₀ ⤳ z := RatModel.gPt_specializes hz _
  have hd0 := hd.1
  have hδd : ‖y₀ ⟨c₀ * S.th d, hth d⟩‖ = (S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    refine le_antisymm (le_ciSup (f := fun x => ‖y₀ ⟨c₀ * S.th x, hth x⟩‖) (Set.finite_range _).bddAbove d)
      (ciSup_le fun x => ?_)
    show ‖y₀ ⟨c₀ * S.th x, hth x⟩‖ ≤ _
    rw [hy₀, hy₀, show ((⟨c₀ * S.th x, hth x⟩ : R') : Ω) = S.th x / S.th d * (c₀ * S.th d) by field_simp,
      RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hd.2 x)) (hle (hth d)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hz (hd.2 x))
  have key : ∀ (h : S.Gam) (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
      ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ *
        (S.rechart c₀ hc R' fg frac hth hev).delta y₀ =
      ‖∑ i, y₀ (algebraMap o R' (S.proj _ (l.wt (m • ν)) i ρ'.i₀)) * y₀ ⟨c₀ * S.ev h i, hev h i⟩‖ := by
    intro h ξ n hn hξ
    let v := RatModel.valHomOf (gPt p ≫ y) z₀ hsp
    have := RatModel.isIntegrallyClosed_O hM z₀
    obtain ⟨ξ', rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (M.O z₀) ξ from ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z₀) hn.ne', by simp [hξ]⟩)
    have n1 : ‖v ξ'‖ = 1 := by
      have e : ξ' ^ n = 1 := Subtype.ext hξ
      have := congrArg (fun t => ‖v t‖) e
      simp only [map_pow, norm_pow, map_one, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    let A : R' := ∑ i, algebraMap o R' (S.proj _ (l.wt (m • ν)) i ρ'.i₀) * ⟨c₀ * S.ev h i, hev h i⟩
    have hA : (A : Ω) = c₀ * partV S yy.ker ρ.i₀ (m • a) h := by
      rw [hker, partV, ← hwt, ← hi, Finset.mul_sum]
      refine (map_sum R'.val _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact mul_left_comm _ _ _
    have hB : IsUnit (⟨c₀ * S.th d, hle (hth d)⟩ : M.O z₀) :=
      (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) _).1 (by
        refine fun h0 => hδ.ne' ?_
        rw [← hδd, hy₀]
        exact norm_eq_zero.2 h0)
    have hF : partV S yy.ker ρ.i₀ (m • a) h / S.th d ∈ M.O z₀ := by
      have := mul_mem (hle A.2) ((RatModel.isUnit_O_iff _).1 hB).2
      rw [hA] at this
      convert this using 1
      field_simp
    have n2 : ‖M.val (gPt p ≫ y) (ξ' : Ω)‖ = 1 := (congrArg norm (RatModel.valHomOf_apply _ _ hsp ξ')).symm.trans n1
    have e₁ : ‖M.val (gPt p ≫ y) ((ξ' : Ω) * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ =
        ‖M.val (gPt p ≫ y) (partV S yy.ker ρ.i₀ (m • a) h / S.th d)‖ := by
      rw [RatModel.val_mul hsp ξ'.2 hF, norm_mul, n2, _root_.one_mul]
    have e₂ : y₀ A = M.val (gPt p ≫ y) (partV S yy.ker ρ.i₀ (m • a) h / S.th d) * y₀ ⟨c₀ * S.th d, hth d⟩ := by
      rw [hy₀, hy₀, ← RatModel.val_mul hsp hF (hle (hth d)), hA]
      congr 1
      field_simp
    refine (congrArg₂ (· * ·) e₁ hδd.symm).trans ?_
    rw [← norm_mul, ← e₂, map_sum]
    simp only [map_mul]
  have hm0 : (m : ℝ) ≠ 0 := by
    have := S.N_ge
    rintro h0
    obtain rfl : m = 0 := by exact_mod_cast h0
    omega
  have hqm : ∀ χ, l.q (m • χ) = (S.N : ℝ) * l.q χ := fun χ => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, congrArg (Nat.cast : ℕ → ℝ) hm]
    simp [sq]
  have hN : (0 : ℝ) < S.N := by have := S.N_ge; positivity
  refine ⟨fun hmin h hh ξ n hn hξ => ?_, fun hmin k hk hkm => ?_⟩
  · have := WeightBound.main GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 uTors_closed _ _ _ ρ' p y₀ u l hint
      (m • ν) (fun v₀ => by
        have e : S.N • v₀ = m • m • v₀ := by rw [← mul_smul, ← sq, ← hm]
        show _ ≤ l.q (m • ν + S.N • v₀)
        rw [e, ← smul_add, hqm, hqm, hq, hq]
        exact mul_le_mul_of_nonneg_left (hmin _ ⟨j v₀, by rw [map_add, map_nsmul]⟩) hN.le) h (hker ▸ hh) ρ'.i₀
    replace this := (key h ξ n hn hξ).trans_le this
    rw [mul_comm, mul_le_mul_iff_right₀ hδ, hqm, hq] at this
    refine this.trans (le_of_eq ?_)
    congr 2
    exact mul_div_cancel_left₀ _ hN.ne'
  · obtain ⟨h, hh, hk0, he⟩ := GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint m k hm hk hkm ν (fun χ hχ => by
      rw [hq, hq]
      exact hmin _ ⟨j χ, by rw [map_add, map_nsmul]⟩ fun e => hχ (by simpa using j.injective e))
    refine ⟨h, hker ▸ hh, hk0, fun ξ n hn hξ => ?_⟩
    have := (key h ξ n hn hξ).trans he
    rwa [mul_comm, mul_right_inj' hδ.ne', hq] at this

end GlobalTheory.UPoinc.USum
