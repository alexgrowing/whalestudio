import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitValue
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVecStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatLog
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsCombTranslatesOfNuGe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsThirdToSixthOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.WeightZeroUnit
open GlobalTheory.ZH.SecValue

theorem quadratic_nonneg {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  obtain ⟨b, hb⟩ := hq.exists_forall_le
  have h0 : q b ≤ 0 := by simpa using hb 0
  have h2 := hb ((2 : ℤ) • b)
  rw [QuadraticMap.map_smul] at h2
  simp only [zsmul_eq_mul] at h2
  push_cast at h2
  have := hb a
  linarith

theorem value_nonneg_all : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {_} _ {D} Q {F} _ _ {v} _ {A} {_} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∀ (t : SecA A F 1) (s : Fam D.toPre F 1) (c : F), U.ExpandsF F 1 w₀ t s → NuGe D Q F v 1 s 0 → ValAt t x e c → 0 ≤ v c := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n hn p x hx e he t s c ht hν hc
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv
    A G hG U w₀ ρ hN n hn p x hx e he
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  have hS : SumV v (coef s p.g w₁) c := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ t s c ht hc
  refine le_of_sumV (q := 0) hS fun χ => ?_
  refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm 1 le_rfl w₁ s hw₁).2 _ _ 0 (hqk n hn p) hv₁ hν χ)
  have h0 : 0 ≤ Q (n • χ + p.y) := by
    by_cases e : n • χ + p.y = 0
    · rw [e, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ e)
  have e₁ := QForm.two_Q_eq hϖ D hQ (n • χ + p.y)
  have e₂ := QForm.two_Q_eq hϖ D hQ χ
  have e₃ := QForm.two_Q_eq hϖ D hQ p.y
  have e₄ : QForm.bHom hϖ D hQ χ p.y = QForm.bHom hϖ D hQ p.y χ := QForm.bOf_comm D χ p.y
  rw [← QForm.bHom_apply hϖ D hQ] at e₁ e₂ e₃ ⊢
  simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, nsmul_eq_mul, e₄, ← e₂, ← e₃] at e₁
  have h1 : (0 : ℤ) ≤ n ^ 2 * Q χ + n * QForm.bHom hϖ D hQ p.y χ + Q p.y := by nlinarith
  have h2 : (0 : ℚ) ≤ n ^ 2 * Q χ + n * QForm.bHom hϖ D hQ p.y χ + Q p.y := by exact_mod_cast h1
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  refine le_of_le_of_eq (div_nonneg h2 (sq_nonneg (n : ℚ))) ?_
  field_simp
  push_cast
  ring

theorem comb_of_fixed {K M J : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [Fintype J] (f : M ≃ₗ[K] M)
    {c : K} {σ : M} {b : J → K} {s : J → M} {r : J → J → K} (h : c • σ = ∑ j, b j • s j) (fix : f σ = σ)
    (hs : ∀ i, f (s i) = ∑ j, r j i • s j) : c • σ = ∑ i, b i • ∑ j, r j i • s j := by
  rw [← fix, ← map_smul, h, map_sum]
  simp only [map_smul, hs]

theorem comb_comb {F K M I J : Type} [CommSemiring F] [CommSemiring K] [AddCommMonoid M] [Module K M] [Fintype I]
    [Fintype J] (κ : F →+* K) {σ : M} {a : I → F} {t : I → M} {s : J → M} {r : I → J → F}
    (h : σ = ∑ i, κ (a i) • t i) (ht : ∀ i, t i = ∑ j, κ (r i j) • s j) : σ = ∑ j, κ (∑ i, a i * r i j) • s j := by
  rw [h]
  simp only [ht, Finset.smul_sum, map_sum, Finset.sum_smul, map_mul, mul_smul]
  exact Finset.sum_comm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem level_pos (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)

theorem eq_proj_zero {F : Type} [Field F] (φ : o →+* F) (T : AddSubgroup S.Gam) (b e : S.J → F) (c : F)
    (h : ∀ t ∈ T, c = ∑ l, b l * ∑ j, φ (S.ρ t j l) * e j) : c = ∑ i, b i * ∑ j, φ (S.proj T 0 j i) * e j := by
  have : NeZero (S.r * S.N) := ⟨Nat.one_le_iff_ne_zero.1 (level_pos S)⟩
  have := Fintype.ofFinite T
  have hu : IsUnit (Nat.card T : o) := by
    have hd := AddSubgroup.card_addSubgroup_dvd_card T
    rw [Nat.card_fun, Nat.card_zmod] at hd
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (by rw [Nat.cast_pow]; exact S.unit.pow _)
  have e₁ : φ (Ring.inverse (Nat.card T : o)) * (Nat.card T : F) = 1 := by
    rw [← map_natCast φ, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  have e₂ : ∀ j i, φ (S.proj T 0 j i) = φ (Ring.inverse (Nat.card T : o)) * ∑ t : T, φ (S.ρ t j i) := fun j i => by
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.sum_apply]
  calc c = φ (Ring.inverse (Nat.card T : o)) * ∑ t : T, c := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← _root_.mul_assoc, e₁,
          _root_.one_mul]
    _ = φ (Ring.inverse (Nat.card T : o)) * ∑ t : T, ∑ l, b l * ∑ j, φ (S.ρ t j l) * e j := by
        rw [Finset.sum_congr rfl fun (t : T) _ => h t t.2]
    _ = _ := by
        simp only [e₂, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring

theorem exists_eq_smul (a : S.Gam) (h : S.N • a = 0) : ∃ b, a = S.r • b := by
  have : NeZero (S.r * S.N) := ⟨Nat.one_le_iff_ne_zero.1 (level_pos S)⟩
  have : ∀ i, ∃ b : ZMod (S.r * S.N), a i = S.r • b := fun i => by
    have e : ((S.N * (a i).val : ℕ) : ZMod (S.r * S.N)) = 0 := by
      have := congrFun h i
      rw [Pi.smul_apply, nsmul_eq_mul] at this
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact this
    rw [ZMod.natCast_eq_zero_iff, mul_comm S.N] at e
    obtain ⟨b, hb⟩ := Nat.dvd_of_mul_dvd_mul_right (lt_of_lt_of_le two_pos S.N_ge) e
    exact ⟨b, by rw [← ZMod.natCast_zmod_val (a i), hb, Nat.cast_mul, nsmul_eq_mul]⟩
  choose b hb using this
  exact ⟨b, funext hb⟩

variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

theorem charZero (u : ρ.UTest p y₀) : CharZero u.V :=
  RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))

theorem isUnit_of_dvd (u : ρ.UTest p y₀) (hy : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {m : ℕ} (hm : m ∣ S.r * S.N) :
    IsUnit (m : u.V) := by
  obtain ⟨a, ha⟩ := (isUnit_of_dvd_unit (Nat.cast_dvd_cast hm) S.unit : IsUnit (m : o)).exists_right_inv
  obtain ⟨b, hb⟩ := (u.norm_le (u.yK (algebraMap o S.R a))).1 (by
    rw [← RingHom.comp_apply, u.fac]; exact hy a)
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hb, map_natCast, map_one, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R), ← map_mul, ← map_mul,
    ha, map_one, map_one]

theorem pt_nsmul (g : u.Geom) (n : ℕ) (a : S.Gam) : g.pt (n • a) = g.pt a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact left_eq_mul.1 ((congrArg g.pt (add_zero 0).symm).trans (g.pt_add 0 0))
  | succ n ih => rw [succ_nsmul, g.pt_add, ih, pow_succ]

theorem exists_label (g : u.Geom) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (hx : x ^ S.N = 1) :
    ∃ a, x = g.pt (S.r • a) := by
  obtain ⟨a, rfl, -⟩ := g.pt_bij x (by rw [mul_comm, pow_mul, hx, one_pow])
  have e : S.N • a = 0 := (g.pt_bij 1 (one_pow _)).unique ((pt_nsmul g _ _).trans hx)
    (by rw [← zero_smul ℕ (0 : S.Gam), pt_nsmul, pow_zero])
  obtain ⟨b, rfl⟩ := exists_eq_smul a e
  exact ⟨b, rfl⟩

theorem exists_rep (hU : UTorsSt) (l : u.Lab) (g : u.Geom) {a : S.Gam} (ha : a ∈ l.yy.ker) :
    ∃ q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), q.y = 0 ∧
      QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (g.pt a) := by
  have := charZero u
  obtain ⟨f, h1, h2, h3, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) (level_pos S)
  obtain ⟨q, hq⟩ := h2 (g.pt a) (g.fr_tors a).1
  have e := l.yy_eq a q (g.pt a) ((h1 _ _).2 hq.symm) (g.pt_over a)
  rw [AddMonoidHom.mem_ker.1 ha] at e
  obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 e.symm
  refine ⟨TorusExt.qkShift u.D.tau_bimult q (-z), ?_,
    (h1 _ _).2 (hq.symm.trans ((h3 _ _).2 (TorusExt.equiv_qkShift u.D.tau_bimult q (-z))))⟩
  show q.y + (S.r * S.N) • (-z) = 0
  rw [← hz, smul_neg]
  exact add_neg_cancel _

set_option maxHeartbeats 2000000 in

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ p _ y₀ u l hy h hh
  have hTB := GlobalTheory.twistBaseChange
  obtain ⟨h3, h4, h5, -⟩ := GlobalTheory.laws_third_to_sixth_of_laws hL hTB
  have hLL : LL := ⟨hL, hL2, h3, h4, h5⟩
  have hT := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hTW := (GlobalTheory.twisting_statements_of_laws hL hTB).1
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hL.globalFns hTB
  have := charZero u
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  obtain ⟨v, hv, -, hvn⟩ := GlobalTheory.NormValuation.main p u.V u.norm_le ϖ hϖ
  obtain ⟨g⟩ := GlobalTheory.ZH.utest_geom_nonempty hL o Ω S ρ p y₀ u
  obtain ⟨w₀, hw₀⟩ := (GlobalTheory.UT.EvalZero.value_at_origin hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p)).2.1
    g.rig g.rig_gen
  obtain ⟨th', ϑ, hϑ, hprim, hgen⟩ := GlobalTheory.UT.exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1
  obtain ⟨c₀, hc⟩ := hgen g.th
  obtain ⟨c, rfl⟩ := kon_surj c₀
  have hcomb : IsComb (fun _ : Unit => th') (fun _ => c) g.th := fun j => by
    rw [Fintype.sum_unique]; exact hc j

  have hδ : S.delta y₀ ≤ ‖c‖ := by
    have : NeZero (S.r * S.N) := ⟨Nat.one_le_iff_ne_zero.1 (level_pos S)⟩
    obtain ⟨x, hx⟩ : ∃ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀ := exists_eq_ciSup_of_finite
    obtain ⟨f, h1, h2, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) (level_pos S)
    obtain ⟨q, hq⟩ := h2 (g.pt x) (g.fr_tors x).1
    have hqx := (h1 _ _).2 hq.symm
    obtain ⟨c', hc'⟩ := ValM.exists hL (SecM.ofSec u.A.A th') (g.fr_tors x).2.1
    have h0 := value_nonneg_all hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv u.A u.G u.semi u.U
      w₀ g.rig hw₀ _ (level_pos S) q _ hqx _ (g.fr_tors x) th' ϑ c' hϑ hprim.1 hc'
    have e := hc'.smul c
    rw [← Fintype.sum_unique (fun _ : Unit => kon u.V (PadicAlgCl p) c • SecM.ofSec u.A.A th'),
      ← (isComb_iff _ _ _).1 hcomb] at e
    rw [← hx, ValM.unique (σ := SecM.ofSec u.A.A g.th) (g.th_val x) e, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hvn c').1.1 h0)

  have hn3 : 3 ≤ ρ.n := by
    have := ρ.n_prime.two_le
    obtain ⟨a, ha⟩ := ρ.n_odd
    omega
  have hm3 : 3 ≤ ρ.n ^ ρ.k := hn3.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  have hN4 : 4 ≤ S.N := by rw [ρ.N_eq]; nlinarith
  have hNo : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  obtain ⟨q, hq, hqx⟩ := exists_rep hU l g hh
  obtain ⟨s, hν, hsupp, hunit⟩ := exists_unit_value hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ g.rig hw₀ _ S.N (level_pos S) hN4 q _ hq hqx _ (g.fr_tors h)
  obtain ⟨σ, hσ, -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hA u.D u.A u.G u.semi u.U).1 (PadicAlgCl p) S.N
    hNo.pos w₀ hw₀.1).2 s
  obtain ⟨c', hc'⟩ := ValM.exists hL (SecM.ofSec u.A.A σ) (g.fr_tors h).2.1
  have hc1 : ‖c'‖ = 1 := (hvn c').2.1 (hunit σ c' hσ hc')

  obtain ⟨act, hact, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns _ u.A (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  have hU_act : ∀ a i, act (g.U a) (SecM.ofSec u.A.A (g.s i)) =
      ∑ j, kon u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a j i))) • SecM.ofSec u.A.A (g.s j) := fun a i =>
    (isComb_iff _ _ _).1 ((g.U_act a i (SecM.toSec u.A.A (act (g.U a) (SecM.ofSec u.A.A (g.s i))))).1
      ((hact _ _ _).2 rfl))
  obtain ⟨n, a, x, t, hx, hsum⟩ := GlobalTheory.ZH.exists_isComb_translates_of_nuGe hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ g.rig hw₀ th' ϑ hϑ hprim (ρ.n ^ ρ.k) S.N ρ.n_odd.pow
    (isUnit_of_dvd u hy (by rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _)) hm3 ρ.N_eq g.th c hcomb
    g.α (g.s ρ.i₀) g.α_gen g.α_norm g.s_zero σ (SecM.toSec u.A.A (kon u.V (PadicAlgCl p) c • SecM.ofSec u.A.A σ)) s hσ hν
    ((isComb_iff _ _ _).2 (by rw [Fintype.sum_unique]; rfl))
  choose lab hlab using fun i => exists_label g (x i) (hx i).2.1
  have ht : ∀ i, SecM.ofSec u.A.A (t i) = ∑ j, kon u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ (lab i) j ρ.i₀))) •
      SecM.ofSec u.A.A (g.s j) := fun i =>
    ((hact _ _ _).1 ((hx i).2.2 (g.U (lab i)) (hlab i ▸ g.U_sym (lab i)))).symm.trans (hU_act _ _)
  let b : S.J → PadicAlgCl p := fun j => ∑ i, a i * y₀ (algebraMap o S.R (S.ρ (lab i) j ρ.i₀))
  have hb : ∀ j, ‖b j‖ ≤ 1 := fun j => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
    rw [norm_mul]
    exact mul_le_one₀ ((hvn _).1.1 (hx i).1) (norm_nonneg _) (hy _)
  have hσb : kon u.V (PadicAlgCl p) c • SecM.ofSec u.A.A σ =
      ∑ j, kon u.V (PadicAlgCl p) (b j) • SecM.ofSec u.A.A (g.s j) :=
    comb_comb (kon u.V (PadicAlgCl p)) ((isComb_iff _ _ _).1 hsum) ht

  have key := eq_proj_zero (y₀.comp (algebraMap o S.R)) (S.perp l.yy.ker) b (fun j => y₀ ⟨S.ev h j, S.ev_mem h j⟩)
    (c * c') fun a ha => by
      obtain ⟨q', τ, hq', hτ, hqa, hτv⟩ := GlobalTheory.ZH.PerpTorus.exists_torus_point hLL hU o Ω S ρ p y₀ u l g a ha
      have fix : act (g.U a) (SecM.ofSec u.A.A σ) = SecM.ofSec u.A.A σ := congrArg (SecM.ofSec u.A.A)
        (act_fix hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hNo q' τ _ hq' hτ hqa (g.U a) (g.U_sym a)
          w₀ hw₀.1 σ (SecM.toSec u.A.A (act (g.U a) (SecM.ofSec u.A.A σ))) s hσ (fun β => by
            by_cases hβ : ∀ z : u.D.toPre.X, β ≠ S.N • z
            · exact .inr (hsupp β hβ)
            · obtain ⟨z, hz⟩ := not_forall.1 hβ
              obtain rfl := not_not.1 hz
              refine .inl (Units.ext ?_)
              rw [hτv, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ZMod.val_zero,
                pow_zero, map_one, map_one, Units.val_one]) ((hact _ _ _).2 rfl))
      have e := hc'.smul c
      rw [comb_of_fixed (act (g.U a)) hσb fix (hU_act a)] at e
      exact e.unique (ValM.sum hL (g.fr_tors h).2.1 _ fun i =>
        (ValM.sum hL (g.fr_tors h).2.1 _ fun j => ValM.smul (σ := SecM.ofSec u.A.A (g.s j)) (g.ev_val h j) _).smul _)
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty (t := Finset.univ) Finset.univ_nonempty
    fun i => b i * ∑ j, (y₀.comp (algebraMap o S.R)) (S.proj (S.perp l.yy.ker) 0 j i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩
  rw [← key, norm_mul, norm_mul, hc1, _root_.mul_one] at hi
  have hle := GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hU o Ω S ρ p y₀ u l hy 0 (fun v₀ => by
    rw [map_zero]; exact quadratic_nonneg _ l.pos _) h hh i
  rw [map_zero l.q, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] at hle
  refine ⟨i, le_antisymm hle ?_⟩
  rw [map_zero l.wt]
  exact hδ.trans (hi.trans (mul_le_of_le_one_left (norm_nonneg _) (hb i)))

end GlobalTheory.ZH.WeightZeroUnit
end
