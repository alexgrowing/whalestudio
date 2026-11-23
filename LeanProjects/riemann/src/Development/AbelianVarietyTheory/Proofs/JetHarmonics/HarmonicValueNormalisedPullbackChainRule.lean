import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ChainRule

section Formal

open GlobalTheory.FrameGeo GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB

variable {S : Type} [CommRing S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem toK_self {n : ℕ} (f : PS S n d) : FB.toK S f = f := by
  ext e
  simp [FB.toK]

theorem actK_self (B : FB S d O) (a : O) : B.actK S a = B.A.act a := funext fun _ => toK_self _

variable [Algebra ℚ S] {B : FB S d O} {h : PS S 2 d}

theorem isExpOf_prod' (hh : B.IsCanonGauge S h) (b c : O) (n : ℕ) :
    IsExpOf (∏ i ∈ Finset.range n, ev ![B.A.act b, B.A.act ((i : O) * c), B.A.act c] B.ph2)
      ((n : S) • ev ![B.actK S b, B.actK S c] h - ev ![B.actK S b, B.actK S ((n : O) * c)] h +
        ev ![B.actK S b, B.actK S 0] h) := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, Nat.cast_zero, Nat.cast_zero, zero_smul, zero_mul, zero_sub, neg_add_cancel]
    exact IsExpOf.one
  | succ j ih =>
    have := ih.mul (isExpOf_canonical_gauge hh b ((j : O) * c) c)
    rw [Finset.prod_range_succ]
    convert this using 1
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul, add_mul, _root_.one_mul]
    ring

theorem exists_series (hh : B.IsCanonGauge S h) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O)) :
    ∃ w : PS S 1 d, FB.toK S w = FB.expS S (ev (n := 1) ![B.actK S a] (B.hL S h w0) - (N : S) • B.hL S h w0) ∧
      w * ∏ i ∈ Finset.range N, ev ![B.A.act 1, B.A.act ((i : O) * w0), B.A.act w0] B.ph2 =
        ev ![B.A.act 1, B.A.act (w0 * a)] (B.ad a) * ev ![B.A.act 1, B.A.act 0, B.A.act 0] B.ph2 := by
  have h1 := isExpOf_ad hh a 1 (w0 * a)
  have h2 := isExpOf_prod' hh 1 w0 N
  have h3 := isExpOf_canonical_gauge hh 1 0 0
  have e : star a * (w0 * a) = (N : O) * w0 := by rw [← hN]; ring
  rw [e, _root_.mul_one] at h1
  rw [add_zero] at h3
  have h4 := h1.mul h3
  refine ⟨_, toK_self _, ?_⟩
  have c := congrArg₂ (· - ·) h4.1 h2.1
  simp only [← map_sub, sub_zero] at c
  rw [← toK_self (∏ i ∈ _, _), h2.2, ← toK_self (_ * ev _ B.ph2), h4.2, ev_actK_hL, hL_eq]
  unfold FB.expS
  rw [← WickVanishing.exp_add (by convert c using 2; ring) h2.1]
  congr 1
  ring

end Formal

section Jets

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

variable {S : Type} [CommRing S] {d : ℕ}

def sb (m : ℕ) {n : ℕ} (a : Fin n → Pt S 1 d) : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstPS (m := m) fun p : Fin n × Fin d => a p.1 p.2

variable {m n : ℕ} {a : Fin n → Pt S 1 d} (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
include ha

theorem sb_X (i : Fin n) (j : Fin d) :
    sb m a (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) = Formalism.L2.Pj.psJet m (a i j) := by
  rw [sb, jetSubstPS_X m (fun p : Fin n × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) (i, j)]

theorem sb_psJet (f : PS S n d) : sb m a (Formalism.L2.Pj.psJet m f) = Formalism.L2.Pj.psJet m (ev a f) := by
  rw [sb, ev, jetSubstPS_psJet m (fun p : Fin n × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f]

theorem sb_psIn {n' : ℕ} (r : Fin n' → Fin n) (f : PS S n' d) :
    sb m a (Ideal.Quotient.mk _ (psIn d m r f)) = Formalism.L2.Pj.psJet m (ev (fun i => a (r i)) f) := by
  rw [← sb_psJet (fun i => ha (r i))]
  have : ((sb m a).comp (Ideal.Quotient.mkₐ S _)).comp
      (MvPolynomial.rename (fun p : Fin n' × Fin d => (r p.1, p.2))) =
      (sb m (fun i => a (r i))).comp (Ideal.Quotient.mkₐ S _) := MvPolynomial.algHom_ext fun p => by
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, Ideal.Quotient.mkₐ_eq_mk]
    exact (sb_X ha _ _).trans (sb_X (fun i => ha (r i)) p.1 p.2).symm
  exact DFunLike.congr_fun this (psTrunc m f)

theorem sb_comp {n' : ℕ} {b : Fin n' → Pt S 1 d} (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0)
    (φ : Fin n' × Fin d → MvPolynomial (Fin n × Fin d) S) (h0 : ∀ p, MvPolynomial.constantCoeff (φ p) = 0)
    (hφ : ∀ p, sb m a (Ideal.Quotient.mk _ (φ p)) = Formalism.L2.Pj.psJet m (b p.1 p.2)) :
    (sb m a).comp (jetSubstP m φ) = sb m b := by
  apply jet_hom_ext
  intro p
  rw [sb_X hb p.1 p.2, ← hφ]
  simp only [AlgHom.comp_apply, jetSubstP, jetMap_mk, MvPolynomial.aeval_X, h0, map_zero, sub_zero]

theorem sb_copy (i : Fin n) :
    (sb m a).comp (jetCopy d m i) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a i p.2) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, jetMap_mk, MvPolynomial.aeval_X, ExpGB.cc_psTrunc', ha, map_zero,
    sub_zero]
  exact sb_X ha _ _

omit ha in
theorem cc_psIn {n' : ℕ} (r : Fin n' → Fin n) (f : PS S n' d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  rw [psIn, MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', hf]

end Jets

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC in

theorem exists_gen_norm (wP : PrimTy H Xo) (hwP : wP.IsGen) (β : 𝓞 E) (N : ℕ) (hN : β * H.bar β = (N : 𝓞 E))
    (wL : AdTy Xo β) (hwL : wL.IsGen) :
    ∃ mu : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act β).left]
      ![(N : ℤ), -1]), mu.IsGen ∧ ∀ (T : Over Xo.X) (y : T ⟶ Xo.univ.t.G) (z : T.left) (J), Good Xo.univ.t.PP.L z J →
        val mu y.left z J * val wP (y ≫ Xo.univ.t.act.act β).left z J *
          ∏ i ∈ Finset.range N, cubV Xo.univ.t.cub z J (y ≫ Xo.univ.t.act.act ((i : 𝓞 E) * H.w0))
            (y ≫ Xo.univ.t.act.act H.w0) y =
        val wP y.left z J ^ N * val wL (lift y (y ≫ Xo.univ.t.act.act (H.w0 * β))).left z J := by
  obtain ⟨t, ht, vt⟩ := exists_cubN Xo.univ.t.cub (1 : Xo.univ.t.G ⟶ Xo.univ.t.G) (Xo.univ.t.act.act H.w0) (𝟙 _) N
  obtain ⟨mu, hmu, hv⟩ := exists_gen Xo.univ.t.PP.isLB (K' := Fin 2)
    (φ' := ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act β).left]) (ε' := ![(N : ℤ), -1]) (fun U _ h => by
      have e₁ : Xo.univ.t.act.act (H.w0 * β) ≫ Xo.univ.t.act.act (H.bar β) = Xo.univ.t.act.act H.w0 ^ N := by
        rw [← Xo.univ.t.act.mul, _root_.mul_assoc, hN, mul_comm, FrameGeo.act_natCast_mul]
      have e₂ : Xo.univ.t.act.act β ≫ Xo.univ.t.act.act H.w0 = Xo.univ.t.act.act (H.w0 * β) := by
        rw [← Xo.univ.t.act.mul, mul_comm]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [FrameGeo.prod_nmul _ _ N rfl]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, prod_cφ2,
        Fin.prod_univ_one, comp_cφ, Fin.prod_univ_eight, Fin.prod_univ_two, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id, Category.id_comp,
        e₁, e₂, _root_.mul_one, _root_.one_mul]
      rw [mul_comm (Xo.univ.t.act.act H.w0 ^ N) (𝟙 _), mul_comm (Xo.univ.t.act.act H.w0) (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Over.id_left]
      module)
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (GeneratorPullback.powGen Xo.univ.t.PP.L _ _ wP N)
      (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (𝟙 _) (Xo.univ.t.act.act (H.w0 * β))).left))
      (LB.invGen Xo.univ.t.PP.L _ _ (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ wP (Xo.univ.t.act.act β).left) t)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (FrameGeo.powGen_isGen _ _ _ _ hwP N)
      (DVR.pullGen_isGen _ _ _ _ hwL _)) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hwP _) ht)))
  refine ⟨mu, hmu, fun T y z J hJ => ?_⟩
  have e₁ : cubN (cubV Xo.univ.t.cub z J) N (y ≫ 1) (y ≫ Xo.univ.t.act.act H.w0) (y ≫ 𝟙 _) =
      ∏ i ∈ Finset.range N, cubV Xo.univ.t.cub z J (y ≫ Xo.univ.t.act.act ((i : 𝓞 E) * H.w0))
            (y ≫ Xo.univ.t.act.act H.w0) y := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MonObj.comp_one, _root_.one_mul, Category.comp_id, FrameGeo.act_natCast_mul, MonObj.comp_pow]
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, FrameGeo.val_powGen, val_pull hJ, val_pull hJ,
    vt T y z J hJ, e₁, ← Over.comp_left, ← Over.comp_left, comp_lift, Category.comp_id]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem one_left (T : Over Xo.X) : (1 : T ⟶ Xo.univ.t.G).left = (toUnit T).left ≫ eSec Xo.univ.t.G := rfl

open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC in

theorem val_norm (wP : PrimTy H Xo) (hwP : IsPrim wP) (β : 𝓞 E) (N k : ℕ) (hN : β * H.bar β = (N : 𝓞 E))
    (wL : AdTy Xo β) (hwL : wL.IsGen)
    (α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act β).left]
      ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hα : α.IsGen)
    (hn : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ α (eSec Xo.univ.t.G))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig ((k * N : ℕ) : ℤ))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-(k : ℤ)))))
    {T : Over Xo.X} (y : T ⟶ Xo.univ.t.G) {z : T.left} {J} (hJ : Good Xo.univ.t.PP.L z J)
    (h1 : val wL (lift (1 : T ⟶ Xo.univ.t.G) (1 : T ⟶ Xo.univ.t.G)).left z J = 1) :
    val α y.left z J * (val wP (y ≫ Xo.univ.t.act.act β).left z J *
          ∏ i ∈ Finset.range N, cubV Xo.univ.t.cub z J (y ≫ Xo.univ.t.act.act ((i : 𝓞 E) * H.w0))
            (y ≫ Xo.univ.t.act.act H.w0) y) ^ k =
        (val wP y.left z J ^ N * val wL (lift y (y ≫ Xo.univ.t.act.act (H.w0 * β))).left z J) ^ k := by
  obtain ⟨mu, hmu, hv⟩ := exists_gen_norm wP hwP.1 β N hN wL hwL
  obtain ⟨nu, hnu, hw⟩ := exists_gen Xo.univ.t.PP.isLB (K' := Fin 2)
    (φ' := ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act β).left]) (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)]) (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul, mul_neg, _root_.mul_one])
    (GeneratorPullback.powGen Xo.univ.t.PP.L _ _ mu k) (FrameGeo.powGen_isGen _ _ _ _ hmu k)
  obtain ⟨a, -, va⟩ := FrameGeo.exists_ratio Xo.univ.t.PP.isLB Xo.univ.t.G.hom η[Xo.univ.t.G].left
    (Over.w η[Xo.univ.t.G]) (GlobalTheory.SemiRigid.globalFns _ _ (isAbelianScheme_univ Xo)).2 hα hnu
  have o : ∀ b, (1 : T ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act b = 1 := fun b => by
    haveI := Xo.univ.t.act.hom b
    exact MonObj.one_comp _
  have v₁ := hv T 1 z J hJ
  simp only [o, h1, (isCub_cubV Xo.univ.t.cub hJ).face, Finset.prod_const_one, _root_.mul_one] at v₁
  have v₂ := (val_pull hJ _ _ _).symm.trans (val_corr hJ hwP.2 (toUnit T).left)
  have v₃ := (val_pull hJ _ _ _).symm.trans (val_corr hJ hn (toUnit T).left)
  rw [val_mul hJ, ExpGE.val_rigPow, ExpGE.val_rigPow, ← v₂, ← one_left] at v₃
  have v₄ : val α (1 : T ⟶ Xo.univ.t.G).left z J = val nu (1 : T ⟶ Xo.univ.t.G).left z J := by
    rw [v₃, hw _ _ z J hJ, FrameGeo.val_powGen, eq_mul_inv_of_mul_eq v₁, mul_pow, zpow_neg, zpow_natCast, zpow_natCast,
      inv_pow, ← pow_mul, mul_comm N k]
  have v₅ := va _ (1 : T ⟶ Xo.univ.t.G).left z J hJ
  rw [v₄, Over.w] at v₅
  have v₆ := va _ y.left z J hJ
  rw [Over.w, (Units.mul_left_inj _).1 (v₅.symm.trans (_root_.one_mul _).symm), _root_.one_mul] at v₆
  rw [Units.ext v₆, hw _ _ z J hJ, FrameGeo.val_powGen, ← mul_pow, ← _root_.mul_assoc, hv T y z J hJ]

end Global

section Sec

variable {X : Scheme.{0}} {A : Over X} [GrpObj A] {L : LB A.left} {T T' : Over X} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem sval_pullSec {a : ℤ} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s') (t : Z ⟶ (T' ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T' A).left) (ε := fun _ => a) s' t z J =
      sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ h.left) z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T' A).left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ h.left) z J
    (fun _ => J (t ≫ (snd T' A).left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])]
  exact (congrArg (gs t z _) (H _)).trans ((gs_res _ z _ hy _).trans (gs_pull t h.left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ (snd T' A).left)))
    (chart_le_res A L h hh a _ hy) _))

theorem sval_twistPull {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val *
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

end Sec

section Chart

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S} (C : ChartAt Xo c y) (m : ℕ)

abbrev sg {n : ℕ} (v : Fin n → 𝓞 E) : jO y C.d m 1 ⟶ jO y C.d m n :=
  homAt y.x (sb m fun i => C.B.A.act (v i))

abbrev px (a : 𝓞 E) : jO y C.d m 1 ⟶ Xo.univ.t.G := C.x m ≫ Xo.univ.t.act.act a

theorem sg_jpt {n : ℕ} (v : Fin n → 𝓞 E) (i : Fin n) : sg C m v ≫ jpt y C.d C.x m i = px C m (v i) := by
  rw [jpt, ← Category.assoc, GermD.homAt_comp, sb_copy (fun i => C.B.A.const (v i)), px, C.chart.act]

theorem jetSubstActionPoints_single_comp_chart_coordinate (a : 𝓞 E) : sg C m ![a] ≫ C.x m = px C m a := by
  rw [← show sg C m ![a] ≫ jpt y C.d C.x m 0 = px C m a from sg_jpt C m ![a] 0, jpt,
    show jetCopy (S := S) C.d m (0 : Fin 1) = AlgHom.id S _ from jet_hom_ext fun p => by
      obtain ⟨p, q⟩ := p
      obtain rfl : p = 0 := Subsingleton.elim _ _
      simp [jetCopy, jetMap_mk], GermD.homAt_id, Category.id_comp]

def jv (z : (jO y C.d m 1).left) : PS S 1 C.d →* ((jO y C.d m 1).left).presheaf.stalk z where
  toFun f := gs (𝟙 _) z ⊤ (toΓ _ (Formalism.L2.Pj.psJet m f))
  map_one' := by rw [FBIdJet.psJet_one, map_one, gs_eq _ z ⊤ trivial, map_one, map_one]
  map_mul' f g := by rw [FBIdJet.psJet_mul, map_mul, gs_mul _ z ⊤ trivial]

variable {m} {z : (jO y C.d m 1).left}

theorem gs_sg {n : ℕ} (v : Fin n → 𝓞 E) (f : PS S n C.d) :
    gs (sg C m v).left z ⊤ (toΓ _ (Formalism.L2.Pj.psJet m f)) = jv C m z (ev (fun i => C.B.A.act (v i)) f) := by
  have e := gs_pull (𝟙 _) (sg C m v).left z ⊤ trivial (toΓ _ (Formalism.L2.Pj.psJet m f))
  rw [Category.id_comp] at e
  refine e.symm.trans (congrArg (gs (𝟙 _) z ⊤) ?_)
  rw [← sb_psJet (fun i => C.B.A.const (v i))]
  exact (congrArg (fun φ => φ.hom (Formalism.L2.Pj.psJet m f)) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (sb m fun i => C.B.A.act (v i) : _ →ₐ[S] _).toRingHom))).symm

theorem gm_sg {n : ℕ} (v : Fin n → 𝓞 E) (f : PS S n C.d) (u : (Jet S (Fin n × Fin C.d) m)ˣ)
    (hu : (u : Jet S (Fin n × Fin C.d) m) = Formalism.L2.Pj.psJet m f) :
    (gm (sg C m v).left z ⊤ (unitΓ u)).val = jv C m z (ev (fun i => C.B.A.act (v i)) f) := by
  rw [← gs_sg, ← hu]
  exact (gs_unit _ z ⊤ trivial _).symm

variable {J : ((jO y C.d m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι}

def ea (z : (jO y C.d m 1).left) (J : ((jO y C.d m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (a b : 𝓞 E) :=
  val (L := Xo.univ.t.PP.L) (φ := cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)]) (ε := cε 2) (C.e m)
    (sg C m ![a, b]).left z J

variable (hJ : Good Xo.univ.t.PP.L z J)
include hJ

theorem val_pe {n : ℕ} (v : Fin n → 𝓞 E) (a b : 𝓞 E) (p q : Fin C.d → MvPolynomial (Fin n × Fin C.d) S)
    (hp : ∀ j, MvPolynomial.constantCoeff (p j) = 0 ∧
      sb m (fun i => C.B.A.act (v i)) (Ideal.Quotient.mk _ (p j)) = Formalism.L2.Pj.psJet m (C.B.A.act a j))
    (hq : ∀ j, MvPolynomial.constantCoeff (q j) = 0 ∧
      sb m (fun i => C.B.A.act (v i)) (Ideal.Quotient.mk _ (q j)) = Formalism.L2.Pj.psJet m (C.B.A.act b j)) :
    val (pe y C.d C.x C.e m ![p, q]) (sg C m v).left z J = ea C z J a b := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, GermD.homAt_comp, sb_comp (fun i => C.B.A.const (v i)) (b := fun i => C.B.A.act (![a, b] i))
    (fun i => C.B.A.const _) _ (fun ⟨i, j⟩ => by fin_cases i; exacts [(hp j).1, (hq j).1])
    (fun ⟨i, j⟩ => by fin_cases i; exacts [(hp j).2, (hq j).2])]
  rfl

omit hJ in
theorem okX {n : ℕ} (v : Fin n → 𝓞 E) (i : Fin n) (a : 𝓞 E) (h : v i = a) (j : Fin C.d) :
    MvPolynomial.constantCoeff (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin C.d) S) = 0 ∧
      sb m (fun i => C.B.A.act (v i)) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        Formalism.L2.Pj.psJet m (C.B.A.act a j) :=
  h ▸ ⟨MvPolynomial.constantCoeff_X _ _, sb_X (fun i => C.B.A.const (v i)) i j⟩

omit hJ in
theorem okA {n : ℕ} (v : Fin n → 𝓞 E) (i : Fin n) (a b : 𝓞 E) (h : v i = b) (j : Fin C.d) :
    MvPolynomial.constantCoeff (psIn C.d m ![i] (C.B.A.act a j)) = 0 ∧
      sb m (fun i => C.B.A.act (v i)) (Ideal.Quotient.mk _ (psIn C.d m ![i] (C.B.A.act a j))) =
        Formalism.L2.Pj.psJet m (C.B.A.act (a * b) j) := by
  subst h
  refine ⟨cc_psIn _ _ (C.B.A.const a j), ?_⟩
  rw [sb_psIn (fun i => C.B.A.const (v i)), C.B.A.mul_act, comp1]
  congr 2
  funext k; fin_cases k; rfl

omit hJ in
theorem okF {n : ℕ} (v : Fin n → 𝓞 E) (i i' : Fin n) (a b : 𝓞 E) (h : v i = a) (h' : v i' = b) (j : Fin C.d) :
    MvPolynomial.constantCoeff (psIn C.d m ![i, i'] (C.B.G.F j)) = 0 ∧
      sb m (fun i => C.B.A.act (v i)) (Ideal.Quotient.mk _ (psIn C.d m ![i, i'] (C.B.G.F j))) =
        Formalism.L2.Pj.psJet m (C.B.A.act (a + b) j) := by
  subst h h'
  refine ⟨cc_psIn _ _ (C.B.G.const j), ?_⟩
  rw [sb_psIn (fun i => C.B.A.const (v i)), C.B.A.add_act, FGLaw.add, addOf]
  congr 2
  funext k; fin_cases k <;> rfl

theorem val_eL (a : 𝓞 E) : val (eL y C.d C.x C.B.A.act C.e C.wP m) (sg C m ![a]).left z J =
    val C.wP (px C m a).left z J * ea C z J a (H.w0 * a) := by
  rw [eL, val_mul hJ, val_pull hJ, ← Over.comp_left, jetSubstActionPoints_single_comp_chart_coordinate, val_pe C hJ ![a] a (H.w0 * a) _ _ (okX C _ 0 _ rfl) (okA C _ 0 _ _ rfl)]

theorem cub_eq (a b b' : 𝓞 E) :
    (cubV Xo.univ.t.cub (T := jO y C.d m 1) z J (px C m b) (px C m b') (px C m a) *
        (ea C z J a b * ea C z J a b')).val =
      jv C m z (ev ![C.B.A.act a, C.B.A.act b, C.B.A.act b'] C.B.ph2) * (ea C z J a (b + b')).val := by
  obtain ⟨u, hu, hc⟩ := C.frame.ph2 m
  have v := val_corr hJ hc (sg C m ![a, b, b']).left
  have p₀ : sg C m ![a, b, b'] ≫ jpt y C.d C.x m 0 = px C m a := sg_jpt C m _ _
  have p₁ : sg C m ![a, b, b'] ≫ jpt y C.d C.x m 1 = px C m b := sg_jpt C m _ _
  have p₂ : sg C m ![a, b, b'] ≫ jpt y C.d C.x m 2 = px C m b' := sg_jpt C m _ _
  have q₁ := val_pe C hJ ![a, b, b'] a (b + b') _ _ (okX C _ 0 a rfl) (okF C _ 1 2 b b' rfl rfl)
  have q₂ := val_pe C hJ ![a, b, b'] a b _ _ (okX C _ 0 a rfl) (okX C _ 1 b rfl)
  have q₃ := val_pe C hJ ![a, b, b'] a b' _ _ (okX C _ 0 a rfl) (okX C _ 2 b' rfl)
  rw [val_cub _ _ hJ, p₀, p₁, p₂, ExpGD.val_scale' _ _ _ _ _ _ _ hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    q₁, q₂, q₃, ← mul_inv, ← _root_.mul_assoc, eq_mul_inv_iff_mul_eq] at v
  have e : (fun i => C.B.A.act (![a, b, b'] i)) = ![C.B.A.act a, C.B.A.act b, C.B.A.act b'] := by
    funext i; fin_cases i <;> rfl
  rw [← e, ← gm_sg C _ _ u hu]
  exact congrArg Units.val v

theorem ad_eq (β : 𝓞 E) (wL : ExpGC.AdTy Xo β) (hrel : ExpGD.AdRel C β wL) (a b : 𝓞 E) :
    (val wL (lift (px C m a) (px C m b)).left z J * ea C z J (β * a) b).val =
      jv C m z (ev ![C.B.A.act a, C.B.A.act b] (C.B.ad β)) * (ea C z J a (H.bar β * b)).val := by
  obtain ⟨u, hu, hc⟩ := hrel m
  have v := val_corr hJ hc (sg C m ![a, b]).left
  have p₀ : sg C m ![a, b] ≫ jpt y C.d C.x m 0 = px C m a := sg_jpt C m _ _
  have p₁ : sg C m ![a, b] ≫ jpt y C.d C.x m 1 = px C m b := sg_jpt C m _ _
  have q₁ := val_pe C hJ ![a, b] (β * a) b _ _ (okA C _ 0 β a rfl) (okX C _ 1 b rfl)
  have q₂ := val_pe C hJ ![a, b] a (H.bar β * b) _ _ (okX C _ 0 a rfl) (okA C _ 1 (H.bar β) b rfl)
  rw [ExpGD.val_scale' _ _ _ _ _ _ _ hJ, val_mul hJ, val_pull hJ, ← Over.comp_left, comp_lift, p₀, p₁, q₁, q₂] at v
  have e : (fun i => C.B.A.act (![a, b] i)) = ![C.B.A.act a, C.B.A.act b] := by
    funext i; fin_cases i <;> rfl
  rw [← e, ← gm_sg C _ _ u hu]
  exact congrArg Units.val v

theorem sval_germ {k : ℕ} {F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))} {f : PS S 1 C.d}
    (hf : IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) (a : 𝓞 E) :
    sval (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (ptO Xo y.x) Xo.univ.t.G).left) (ε := fun _ => (k : ℤ)) F
      (lift (jBase y C.d m 1) (px C m a)).left z J =
      jv C m z (ev ![C.B.A.act a] f) * ((val C.wP (px C m a).left z J * ea C z J a (H.w0 * a)) ^ k).val := by
  obtain ⟨F', τ, hP, hC, hV⟩ := hf m
  have v₁ := sval_valueAt hV (sg C m ![a]).left hJ
  have v₂ : val τ (sg C m ![a]).left z J = val (eL y C.d C.x C.B.A.act C.e C.wP m) (sg C m ![a]).left z J ^ k :=
    (val_corr hJ hC _).trans (map_pow _ _ _)
  have e₁ : sg C m ![a] ≫ jBase y C.d m 1 = jBase y C.d m 1 := Over.OverMorphism.ext (spMap_comp_alg _)
  have e : (fun i => C.B.A.act (![a] i)) = ![C.B.A.act a] := by
    funext i; fin_cases i; rfl
  rw [sval_pullSec hP _ hJ, ← Over.comp_left, ← Over.comp_left, ptSecT, comp_lift, lift_whiskerRight, Category.comp_id,
    e₁, jetSubstActionPoints_single_comp_chart_coordinate, v₂, val_eL C hJ, gs_sg, e] at v₁
  exact v₁

theorem frame_eq (β : 𝓞 E) (N : ℕ) (hN : β * H.bar β = (N : 𝓞 E)) (wL : ExpGC.AdTy Xo β) (hrel : ExpGD.AdRel C β wL)
    (w : PS S 1 C.d)
    (hw : w * ∏ i ∈ Finset.range N, ev ![C.B.A.act 1, C.B.A.act ((i : 𝓞 E) * H.w0), C.B.A.act H.w0] C.B.ph2 =
      ev ![C.B.A.act 1, C.B.A.act (H.w0 * β)] (C.B.ad β) * ev ![C.B.A.act 1, C.B.A.act 0, C.B.A.act 0] C.B.ph2) :
    (val wL (lift (px C m 1) (px C m (H.w0 * β))).left z J * ea C z J β (H.w0 * β)).val =
      jv C m z w * ((∏ i ∈ Finset.range N, cubV Xo.univ.t.cub (T := jO y C.d m 1) z J (px C m ((i : 𝓞 E) * H.w0))
        (px C m H.w0) (px C m 1)) * ea C z J 1 H.w0 ^ N).val := by
  have h1 := ad_eq C hJ β wL hrel 1 (H.w0 * β)
  rw [_root_.mul_one, show H.bar β * (H.w0 * β) = (N : 𝓞 E) * H.w0 by rw [← hN]; ring] at h1
  have h2 : ∀ n : ℕ, ((∏ i ∈ Finset.range n, cubV Xo.univ.t.cub (T := jO y C.d m 1) z J (px C m ((i : 𝓞 E) * H.w0))
        (px C m H.w0) (px C m 1)) * ea C z J 1 H.w0 ^ n * ea C z J 1 0).val =
      jv C m z (∏ i ∈ Finset.range n, ev ![C.B.A.act 1, C.B.A.act ((i : 𝓞 E) * H.w0), C.B.A.act H.w0] C.B.ph2) *
        (ea C z J 1 ((n : 𝓞 E) * H.w0)).val := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have := cub_eq C hJ 1 ((n : 𝓞 E) * H.w0) H.w0
      rw [Finset.prod_range_succ, Finset.prod_range_succ, map_mul, Nat.cast_succ, add_mul, _root_.one_mul,
        _root_.mul_assoc (jv C m z _), ← this, pow_succ]
      simp only [Units.val_mul] at ih ⊢
      linear_combination (cubV Xo.univ.t.cub (T := jO y C.d m 1) z J (px C m ((n : 𝓞 E) * H.w0))
        (px C m H.w0) (px C m 1)).val * (ea C z J 1 H.w0).val * ih
  have h3 := cub_eq C hJ 1 0 0
  rw [show px C m 0 = 1 by rw [px, ExpGC.act_zero, MonObj.comp_one], (isCub_cubV _ hJ).face, _root_.one_mul, add_zero,
    Units.val_mul, Units.mul_left_inj] at h3
  rw [h1, ← Units.mul_left_inj (ea C z J 1 0), _root_.mul_assoc (jv C m z w), ← Units.val_mul, h2, ← _root_.mul_assoc,
    ← map_mul, hw, map_mul, ← h3]
  ring

omit hJ in

theorem germ_eq (β : 𝓞 E) (N k : ℕ) (hN : β * H.bar β = (N : 𝓞 E)) (w : PS S 1 C.d)
    (hw : w * ∏ i ∈ Finset.range N, ev ![C.B.A.act 1, C.B.A.act ((i : 𝓞 E) * H.w0), C.B.A.act H.w0] C.B.ph2 =
      ev ![C.B.A.act 1, C.B.A.act (H.w0 * β)] (C.B.ad β) * ev ![C.B.A.act 1, C.B.A.act 0, C.B.A.act 0] C.B.ph2)
    {F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))}
    {F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k * N : ℕ) (ptO Xo y.x))}
    (hF : IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act β) (k * N : ℕ) k F F') {f f' : PS S 1 C.d}
    (hf : IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) (hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP (k * N) F' f') :
    f' = ev ![C.B.A.act β] f * w ^ k := by
  obtain ⟨α₀, α, h₀, hn, hα, hT⟩ := hF
  obtain ⟨wL, hwL, hrel⟩ := ExpGD.exists_adRel C β
  refine GermFun.psJet_inj fun m => GermFun.toΓ_injective _ (fn_ext fun z _ => ?_)
  choose J hJ using fun χ : (jO y C.d m 1).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ z)
  change jv C m z f' = jv C m z _
  have p1 : ∀ a, px C m 1 ≫ Xo.univ.t.act.act a = px C m a := fun a => by
    rw [px, Category.assoc, ← Xo.univ.t.act.mul, _root_.one_mul]
  have e1 : ev ![C.B.A.act 1] f' = f' := by
    rw [C.B.A.one_act, show (![pt S C.d 0] : Fin 1 → Pt S 1 C.d) = fun j => pt S C.d j by funext j; fin_cases j; rfl,
      JetSer.FBOf.ev_self]
  have v₁ := sval_twistPull hT (lift (jBase y C.d m 1) (px C m 1)).left hJ
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, p1, sval_germ C hJ hf, sval_germ C hJ hf', e1,
    val_corr hJ hα, val_pull hJ, ← Over.comp_left, lift_snd, _root_.mul_one] at v₁
  have h1 := ExpGD.wL_zero C β wL hrel (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) m))).left z J hJ
  rw [← Over.comp_left, comp_lift, MonObj.comp_one] at h1
  have v₂ := val_norm C.wP C.prim β N k hN wL hwL α₀ h₀ hn (px C m 1) hJ h1
  simp only [p1] at v₂
  have v₃ := congrArg (· ^ k) (frame_eq C hJ β N hN wL hrel w hw)
  rw [map_mul, map_pow]
  generalize (∏ i ∈ Finset.range N, cubV Xo.univ.t.cub (T := jO y C.d m 1) z J (px C m ((i : 𝓞 E) * H.w0))
        (px C m H.w0) (px C m 1)) = t at v₂ v₃
  have v₄ := congrArg Units.val v₂
  rw [← Units.mul_left_inj ((val C.wP (px C m 1).left z J * ea C z J 1 H.w0) ^ (k * N)), v₁,
    ← Units.mul_left_inj (t ^ k)]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, mul_comm k N, pow_mul] at v₃ v₄ ⊢
  linear_combination (jv C m z (ev ![C.B.A.act β] f)) * (ea C z J β (H.w0 * β)).val ^ k * v₄ +
    (jv C m z (ev ![C.B.A.act β] f)) * ((val C.wP (px C m 1).left z J).val ^ N) ^ k * v₃

end Chart

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l)

theorem prod_eig {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) (β : 𝓞 E) (m : LtN Dw n →₀ ℕ)
    (hm : ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a (σ, i)) :
    ∏ b, ∏ ℓ : Lt1 Dw, embK c ℓ.1 β ^ colOf m b ℓ = nrm Dw c a β := by
  rw [Finset.prod_comm, Fintype.prod_sigma, nrm]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hm, ← Finset.prod_pow_eq_pow_sum]
  rfl

end Weight

theorem harmonic_value_normPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [Algebra c.F F] (yF : FrPt Xo c F) (β : 𝓞 E) (N k : ℕ) (z : ℤ), β * star β = (N : 𝓞 E) → z = ((k * N : ℕ) : ℤ) → ∀ (n : ℕ) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yF.x))) (hh' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L z (ptO Xo yF.x))), (∀ i, IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act β) z (k : ℤ) (hh i) (hh' i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF z (hh' i) (colOf m i) = algebraMap c.F F (nrm Dw c a β) * ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (k : ℤ) (hh i) (colOf m i) := by
  intro E _ _ _ H Dw l Xo c nab hnab F _ _ yF β N k z hN hz n hh hh' hp a Pp hP
  subst hz
  letI := H.starRing
  letI : Algebra ℚ F := ((algebraMap c.F F).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hpin⟩ := hnab.2 F yF
  obtain ⟨w, hw, hw'⟩ := exists_series C.gauge H.w0 β N hN
  have key : ∀ i mo, nab yF ((k * N : ℕ) : ℤ) (hh' i) mo =
      (∏ ℓ : Lt1 Dw, algebraMap c.F F (embK c ℓ.1 β) ^ mo ℓ) * nab yF (k : ℤ) (hh i) mo := fun i mo => by
    obtain ⟨f, hf⟩ := hex k (hh i)
    obtain ⟨f', hf'⟩ := hex (k * N) (hh' i)
    refine (hpin (k * N) _ f' hf' mo).trans (Eq.trans ?_ (congrArg _ (hpin k _ f hf mo).symm))
    rw [germ_eq C β N k (hnab.1 β ▸ hN) w hw' (hp i) hf hf', mul_comm k N,
      ← nabVal_pullback_monomial F C.d (𝓞 E) F C.B C.h C.gauge H.w0 β N k w hw (Lt1 Dw) C.uvec _ (fun ℓ => ?_) f mo,
      actK_self, toK_self]
    funext j
    have := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c F yF C β ℓ j
    rw [← actK_self] at this
    exact this
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [key]
  rw [Finset.prod_mul_distrib, ← prod_eig c a β m (hP.1.2.2 m hm)]
  simp only [map_prod, map_pow]
  ring

end GlobalTheory.ChainRule
