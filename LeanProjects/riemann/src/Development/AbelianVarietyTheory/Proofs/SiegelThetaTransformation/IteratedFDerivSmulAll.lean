import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GphiEqSmulPhiF
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPt

theorem iteratedFDeriv_smul_all {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (a : ℂ) (F : W → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (a • F) = a • iteratedFDeriv ℂ k F := by
  induction k with
  | zero => ext x m; simp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih, fderiv_const_smul_field]
    funext x
    simp only [Function.comp_apply, Pi.smul_apply, map_smul]

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP I2.polyDeriv
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_smul_all]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem vset_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n M : ℕ} {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem shortRule_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, ‖evR d.Xo₂ d.c₂ d.cδ y₂‖ = 1) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g q0 : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c (algebraMap c.F ℂ) X g q0 n a) (D : SW.Level X) (hn : r ≤ n), Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ L ∈ D.lats, ∀ mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (y : FrPt Xo c ℂ) (A : AnFib X Dc.bas Dc.idx Dc.e x L y) (θ : (Fin g → ℂ) → ℂ), A.Marked mk → A.Reads 1 y.s θ → MeanOne X Dc.bas Dc.idx x L θ → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f : Rul Xo c, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → evR Xo c f y = κ * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ L Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hcomp hlev hnab hcδ ph ψ x₀ hpin r g q0 X a Dc D hn hev hr htie v₀ hv₀ x0
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨ρ₁, s, hρ₁, hg⟩ := GlobalTheory.Dict.GPhi.gphi_eq_smul_phiF E H Dw l Xo c n d hcomp hlev ph ψ x₀ hpin r g X Dc.bas Dc.idx D hn
    Dc.sympl hev hr htie v₀ hv₀ x0
  have hwi : IsIntegral ℤ (H.w0 : E) := htie.w ▸ D.w_int
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := htie.w ▸ D.w_tr
  have hΛ0 : SelfD X X.Λ := (GlobalTheory.SW.level_laws E r X g Dc.bas Dc.idx n Dc.sympl hev D hn).1.1
  refine ⟨fun Λ N => algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n)))⁻¹ *
      (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
      ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) * (((if 0 < s Λ then s Λ else 1 : ℝ)) : ℂ), ?_, ?_⟩
  · intro Λ hΛ N hN
    obtain ⟨-, -, -, hz, hm, -⟩ := GlobalTheory.Dict.ZLat.exists_reps_sum E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt
      X.Λ hΛ0 Λ (vset_one hΛ) N hN.1 (hN.2.2.trans inf_le_left)
    haveI := finite_levQ Dw d.l₂
    have hb : betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n) ≠ 0 := by
      unfold betaH
      split_ifs with h
      · exact h.choose_spec.1
      · exact one_ne_zero
    have hc : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
    refine mul_ne_zero ((_root_.map_ne_zero _).2 ?_) ?_
    · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)) (inv_ne_zero ?_)) ?_
      · exact (_root_.map_ne_zero _).2 hb
      · exact Nat.cast_ne_zero.2 hm.ne'
      · exact Nat.cast_ne_zero.2 hc.ne'
      · exact Nat.cast_ne_zero.2 hz.ne'
    · rw [Complex.ofReal_ne_zero]
      split_ifs with h
      · exact h.ne'
      · exact one_ne_zero
  intro L hL mk δ hmk hδ hx0
  have hLs : SelfD X L := hL.1
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs 1 _
    (Base.stdL_mem_Vset (E := E) n 1)).1
  obtain ⟨ρ₀, hρ₀, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv
  refine ⟨ρ₀ * ρ₁, mul_pos hρ₀ hρ₁, ?_⟩
  intro x hx hux y A θ hA hθ hmean
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp y
  obtain ⟨A₂, hA₂, mk₂, hmk₂, hA₂m, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r g X Dc.bas Dc.idx Dc.e x L y A
    Dc.sympl hx hLs y₂ hy₂ mk hA
  have hth := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r g X Dc.bas Dc.idx Dc.e x L y A Dc.sympl hx hLs θ hθ
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv x hx θ hth
  obtain ⟨t, ht, hgt⟩ := hg L hL mk mk₂ δ v hmk hmk₂ hover hδ hx0 hv
  refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ₀ * t, ?_, ?_⟩
  · rw [norm_mul, norm_mul, hcδ y₂, hnorm x hx hux θ κ₀ hth hmean hκ₀, ht, _root_.one_mul]
  intro Λ hΛ N hN P hP f hf
  obtain ⟨hs, hgt⟩ := hgt Λ hΛ
  have hM : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r X L mk₂ _ hLs hmk₂ (Complex.isPrimitiveRoot_exp _ hM)).2.2.2.2 n N
    hN.1.pos
  obtain ⟨v0, hv0, hfv⟩ := hf ℂ hcomp y y₂ hy₂
  have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X Dc.bas Dc.idx Dc.e x L y₂ A₂ Dc.sympl hx hLs q0 n Dc.hr
    Dc.eL hr hev Dc.dir_eq d.nab₂ hnab θ v κ₀ (hA₂ θ hθ) hv hκ₀ mk₂ hmk₂ hA₂m Λ hΛ N hN Y hY a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (algebraMap c.F ℂ) P := by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext hcomp
  rw [hgt N hN Y hY, theta_smul₂, hmap] at hval
  beta_reduce
  rw [hfv, hval, if_pos hs]
  ring

end GlobalTheory.Dict.ShortPt
