import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.exists_tie_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (R : Subalgebra X.o₁ X.Ω₁) (P' : PolAV (Sp R)) (u' : Sp (ratHull R) ⟶ Xo.XF cf), spMap (ratHull R).val.toRingHom ≫ u' = X.uΩ → UOver Xo cf P' (toRat R) u' → ∃ (G : Over (Sp (ratHull R))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (m : wi.G.left ⟶ G.left) (P₀ : PolAV (Sp X.Ω₁)) (e : P₀.A.left ⟶ wi.G.left), IsGrpPullback G P'.A (spMap (toRat R)) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ IsGrpPullback wi.G G (spMap (ratHull R).val.toRingHom) m ∧ m ≫ β = wi.β ∧ IsGrpPullback P₀.A X.ρ.P.A (spMap X.S.R.val.toRingHom) (e ≫ wi.α) ∧ IsGrpPullback P₀.A P'.A (spMap R.val.toRingHom) (e ≫ m ≫ α) ∧ LBIso P₀.L (X.ρ.P.L.pull (e ≫ wi.α)) ∧ LBIso P₀.L (P'.L.pull (e ≫ m ≫ α)) := by
  intro E _ _ _ H Dw l Xo cf C X wi R P' u' hc h
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hb : IsGrpPullback wi.G Xo.univ.t.G (spMap (ratHull R).val.toRingHom ≫ u' ≫ pullback.fst _ _) wi.β :=
    wi.hβ.congr (by rw [← hc, Category.assoc]) rfl
  have w₁ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact hb.1.w
  have em := hβ.1.lift_fst _ _ w₁
  have hm := hβ.cancel (hb.congr rfl em.symm) (hβ.1.lift_snd _ _ w₁)
  generalize hβ.1.lift _ _ w₁ = m at em hm
  obtain ⟨P₀, φ, hφ, hφL⟩ := exists_pol_baseChange X.ρ.P (spMap X.S.R.val.toRingHom)
  have w₂ : φ ≫ X.ρ.P.A.hom = (P₀.A.hom ≫ 𝟙 _) ≫ spMap X.S.R.val.toRingHom := by
    rw [Category.comp_id]; exact hφ.1.w
  have ee := wi.hα.1.lift_fst _ _ w₂
  have he := wi.hα.cancel (hφ.congr (Category.id_comp _).symm ee.symm) (wi.hα.1.lift_snd _ _ w₂)
  generalize wi.hα.1.lift _ _ w₂ = e at ee he
  subst ee
  have hU := Xo.univ.t.PP.isLB
  refine ⟨G, _, α, β, m, P₀, e, hα, hβ, hL, hm, em, hφ,
    (he.comp (hm.comp hα)).congr ((Category.id_comp _).trans (spMap_val_toRat R)) rfl, hφL, ?_⟩
  have l₁ : LBIso (X.ρ.P.L.pull (e ≫ wi.α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) :=
    GenSpread.lbIso_pull_comp _ rfl rfl wi.hL
  have l₂ : LBIso (P'.L.pull (m ≫ α)) (Xo.univ.t.PP.L.pull (m ≫ β)) := GenSpread.lbIso_pull_comp _ rfl rfl hL
  rw [em] at l₂
  have l₃ : LBIso (P'.L.pull (e ≫ m ≫ α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) := GenSpread.lbIso_pull_comp _ rfl rfl l₂
  exact LBIso.trans P₀.isLB (pull_isLB X.ρ.P.isLB _) (pull_isLB P'.isLB _) hφL
    (LBIso.trans (pull_isLB X.ρ.P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) l₁ l₃.symm)

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.UPoinc.exists_urechart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  intro E _ _ _ H Dw _hpq l Xo cf C X wi w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratLift E H Dw l Xo cf C X w hw
  obtain ⟨U₁, h₁, P₁, _hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w hU₀a hwU₀ hw
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, _hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w hU₁a hwU₁ P₁ X.S.N hN
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf :=
    spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hP' : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat _)).2 ?_
    have := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e] at this
    exact this
  have hcomp : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨G, _, α, β, m, P₀, e, hα, hβ, hαβ, hm, hmβ, ha, ha', hL, hL'⟩ :=
    GlobalTheory.UPoinc.exists_tie_of_uOver E H Dw l Xo cf C X wi (X.M.ringOn U) P' u' hcomp hP'
  have hg' : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ _ ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ _ ha).trans X.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ _ _ ha ha' hL hL' X.ρ.hypS

  obtain ⟨⟨hLw, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI := TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : X.M.ringOn U) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hLw X.S.R.val.toRingHom X.ρ.P P' P₀ _ _ ha ha' hL hL'
    hn hu (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U)
      (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  have frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  have hQ : (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P'.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt' x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P'.A.left, IsGrpPullback P₀.A P'.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P'.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt' x).left := by
    refine ⟨⟨G, inferInstance, α, β, hα, hβ, hαβ, m, hm, hmβ, fun x => ?_⟩, _, ha', hL', hw0⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    exact ⟨w0 ≫ e, by rw [Category.assoc]; exact h₁, by rw [Category.assoc]; exact h₂⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hU', a'', q₂, q₃, q₅⟩, hi₀⟩ := GlobalTheory.ThetaExtend.exists_real_rechart
    GlobalTheory.abelianSchemeLaws_all.1 X.S X.ρ (X.M.ringOn U) fg frac P' P₀ _ _ pt' th b ha ha' hL hL' hg' hyp hadd hbij hweil
    hw0 hth hb
    (fun P pt => (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, ⟨P₀, e ≫ wi.α, a'', ha, q₂, hL, q₃, q₅⟩, hi₀, hU', hcomp⟩
