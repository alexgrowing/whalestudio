import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.RawThetaSup

open GlobalTheory.Dict.ShortPoint

theorem norm_rawThetaSeries_index_bound_le_sqrt {κ t : ℂ} {m z Q : ℕ} {J B : ℝ} {j : ℕ} (hJ : J = j) (hj : 0 < j) (hz : z = m * j)
    (hC : 0 ≤ 1 * (B / Real.sqrt J)) (h : ‖((Q : ℂ))⁻¹ * (κ * t)‖ ≤ 1 * (B / Real.sqrt J)) :
    ‖(1 : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖ ≤ Real.sqrt J * B := by
  have hJ0 : 0 < J := by rw [hJ]; exact_mod_cast hj
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hb : ‖((Real.sqrt J : ℝ) : ℂ)‖ ^ 2 = J := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le, Real.sq_sqrt hJ0.le]
  have h1 := norm_index_cancellation_le_bound hJ hj hz hb hC h
  have e : (1 : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t =
      ((Real.sqrt J : ℝ) : ℂ) * (((Real.sqrt J : ℝ) : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t) := by
    have : ((Real.sqrt J : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact mul_le_mul_of_nonneg_left (h1.trans_eq (_root_.one_mul B)) hs.le

theorem thLaValAt_evR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} {Λ : GenLat E n} {N : ℕ} (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M)
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a)
    (w : (Fin n → LevQ Dw l) → c.F) {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab w Λ N P y (f p y))
    (S : Type) [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    thLaValAt Xo c nab w Λ N P y (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 w 1
  obtain ⟨v, hv, -⟩ := hval S y
  obtain ⟨p, φ, y0, hy0⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c S y
  have e1 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
    p φ y0 y hy0
  have e2 := hnat p.R S φ y0 y hy0 _ v (h p y0) hv
  rw [e1, e2]
  exact hv

set_option maxHeartbeats 1000000 in

theorem norm_evR_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (hct : ∀ k τ, (U.X k).c τ = t) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hDom : Dom a n) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (Λ : GenLat E n) (N : ℕ) (w : (Fin n → LevQ Dw l) → c.F)
    (hw1 : ∀ q, ‖σ (w q)‖ ≤ 1) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (hΛu : Λ.Unimod) (hΛt : Λ.TrivAt l.M)
    (hΛl : Λ.LevOK N l.M) (hP : P ∈ harmL c Λ a) (hf : f ∈ sec Xo c a n)
    (hraw : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab w Λ N P y (f p y))
    (k : U.Comp) (x : (U.X k).dom) (hxo : (U.X k).IsOrtho x.1) (lam : ℝ) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ (U.X k).firstMinimumSq x.1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤
      Real.sqrt (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) *
      ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  have hci := GlobalTheory.chartIndependence_unconditional
  have hr : r = Dw.p + Dw.q := hU.1
  have hn : Even n := hDom.2
  letI A₁ : Algebra c.F ℂ := σ.toAlgebra
  have huf : IsUnitFr (U.X k) x.1 := fun τ i => by
    unfold dmin lminor
    rw [hxo τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp, FD.sgn]
    split_ifs <;> simp
  obtain ⟨W, Dc, A, θ, v, κ, he, hg, hw, hL, hmk, hA, hrd, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr1 a n hDom k x huf
  obtain ⟨-, -, hlen, -, -⟩ := hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 hxo
  have hv0 := thLaValAt_evR nab hnab hΛu hΛt hΛl hP w hf hraw ℂ (unC U k x)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨-, hV, hVd, hstd⟩ := GenLatCmp.genLat_vset E n Λ.La
  have hΛ : Λ.La ∈ Vset E n l.M := hV _ N hM hΛu hΛt hΛl
  have hΛ1 : Λ.La ∈ Vset E n 1 := hVd 1 _ (one_dvd _) hΛ
  obtain ⟨Y, hY⟩ := (GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hΛl.1.pos
  have hval := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A
    Dc.sympl x.2 hL Dw.p n Dc.hr Dc.eL hr hn (he ▸ Dc.dir_eq) nab hnab θ v κ hrd hvac hprod (W.mark k) hmk hA
    Λ.La hΛ N hΛl Y hY a P hP.1 w 1 _ hv0
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)).IsHomogeneous (Formalism.L2.Pj.DF Dw a) :=
    (((GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous E H Dw l c a n).2 P hP.1).map σ).rename_isHomogeneous
  have hcore := fun y => GlobalTheory.T.jet_translate_projected_vacuum_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw _ hL Λ.La hΛ1
    v hvac x.1 x.2 hxo t ht (hct k) θ κ hth hmean hprod lam hlam (fun u hu hu0 => hlam2.trans (hlen u hu hu0)) y _ _
    hhom
  obtain ⟨R, -, -, hR, hR0, -⟩ := VacMean.vac_proj_mean E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn
    H.w0 hw _ hL Λ.La hΛ1 v hvac
  rw [hR] at hR0
  have hJ : (0 : ℝ) < Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r) :=
    Real.sqrt_pos.2 (by exact_mod_cast hR0)
  have hsb : IsSB (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v) := by
    obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _
      H.w0.isIntegral_coe hw _ hL 1 Λ.La hΛ1
    rw [h v hvac.1 v' hv']
    exact isSB_smul _ hv'.1
  rw [sum_coeff_rename] at hcore
  have hc2 := fun y => (le_div_iff₀ hJ).2 (hcore y)
  have hB0 := (norm_nonneg _).trans (hc2 0)
  have hmeanle := norm_mean_le Dc.hr Dc.idx Dc.sympl x.2 (fun q => algebraMap c.F ℂ (w q))
    (fun q => heisG (U.X k) Dc.bas (Y q) (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v))
    (fun q => ((heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn).2.2.2 (Y q) _ hsb).1) _ κ zero_le_one hB0
    hw1 (fun q => hc2 (Y q))
  have hfin := norm_rawThetaSeries_index_bound_le_sqrt (Nat.cast_pow _ r).symm hR0 (zCard_eq Λ hstd hΛl r) (mul_nonneg zero_le_one hB0) hmeanle
  have hev' : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hev', hval, ← hg, index_Ln Λ hstd]
  simp only [map_mul, map_inv₀, map_natCast, map_one]
  exact hfin

end GlobalTheory.RawThetaSup
