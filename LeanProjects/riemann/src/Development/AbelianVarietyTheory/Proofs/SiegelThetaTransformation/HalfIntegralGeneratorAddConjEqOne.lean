import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortRead

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem halfIntegralGenerator_add_conj_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add, cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem sb_smul (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 a

theorem sb_finsum {Q : Type} (f : Q → TF n g) (hf : ∀ q, IsSB (f q)) : IsSB (∑ᶠ q, f q) :=
  finsum_induction (fun φ : TF n g => IsSB φ) isSB_zero
    (fun φ ψ h h' => (isSB_algebra_haar_linear ℚ _ _ φ ψ h h').1) hf

theorem sb_gphi (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {M : ℕ} {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsSB v) {Q : Type} (W : Q → ℂ)
    (Y : Q → Matrix (Fin n) (Fin r) E) : IsSB (gphi X bas w Λ L v W Y) := by
  obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ
  refine sb_finsum _ fun q => sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ _ ?_).1
  rw [h v hv v' hv']
  exact sb_smul _ hv'.1

theorem theta_smul₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {k : X.Ψ → Fin q0 → ℕ} {k' : X.Ψ → Fin X.p0 → ℕ} {φ : TF n g} (hφ : IsSB φ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : P ∈ Harm.rowHighest ℂ k k') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a : ℂ) : thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hφ P hP).2.2.2 x hx
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP
  rw [h, I2.polyDeriv_smul_fun _ _ han.contDiff]

theorem rdU_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (Λ : GenLat E n) (N : ℕ) (rk : Bool) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → AdmX (l := l) rk x0 → P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ f ∈ sec Xo c a n, IsShortRule Xo c d Λ N x0 P f → ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hlev ⟨sr, hnab⟩ hunit hpin W k a hdom Dc hDe Λ N rk x0 P
    hΛ1 hΛ2 hΛ3 hadm hP f hf hshort
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hn : Even n := hdom.2
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨hle, hmap⟩ := admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpq := hle rk x0 hadm
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin hpq
  obtain ⟨-, hL, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : 0 < N := hΛ3.1.pos
  obtain ⟨Λ⟩ := Λ
  have hΛ : Λ ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ).2.1 _ N hM hΛ1 hΛ2 hΛ3
  obtain ⟨v, hv⟩ := (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv
  have hroots : ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ →
      ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ (U.X k).Λ mk₂ N Y := fun mk₂ h =>
    (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hL h (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hN

  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E,
      ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ →
      ∀ Y', IsRoots d.l₂ (U.X k).Λ mk₂ N Y' → ∃ t : ℂ, ‖t‖ = 1 ∧
        gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y' =
          t • gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y := by
    by_cases hex : ∃ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₃ ∧
        MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₃
    · obtain ⟨mk₃, h1, h2⟩ := hex
      obtain ⟨Y, hY⟩ := hroots mk₃ h1
      refine ⟨Y, fun mk₂ h3 h4 Y' hY' => ?_⟩
      obtain ⟨t, ht, h⟩ := GlobalTheory.Dict.MarkMove.gphi_move E H Dw l Xo c n d hlev ph ψ x₀ hph r _ _ Dc.bas Dc.idx Dc.sympl hn hrpq
        (hrpq ▸ hpq) _ hL (W.mark k) mk₂ mk₃ hmk h3 h1 h4 h2
      exact ⟨t, ht, h x0 v hv Λ hΛ N hΛ3 Y' Y hY' hY⟩
    · exact ⟨fun _ => 0, fun mk₂ h3 h4 => absurd ⟨mk₂, h3, h4⟩ hex⟩
  have hG := sb_gphi Dc.idx Dc.sympl hn hw hw' hL hΛ hv.1 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y
  generalize gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = G at hY hG
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c ⟨Λ⟩))⁻¹ *
    (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
    ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) := ⟨_, rfl⟩
  have hP' := Dc.mem P hP
  have huG := sb_smul u hG
  have hsec := hU.2.2.2.2.1 a n hdom f hf k
  have hth := theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ huG _ hP'
  rw [Dc.wt_eq] at hth
  obtain ⟨C, -, hC⟩ := const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (u • G) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hsec.1, hth.1, fun x hx b hb => ⟨hsec.2.1 x hx b hb, hth.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC U k ⟨x, hx⟩)
      obtain ⟨B, hB, mk₂, hmk₂, hBm, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e x _
        _ A Dc.sympl hx hL y₂ hy₂ _ hA
      have hT := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hL θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv x hx θ hT
      have hκn := hnorm x hx hux θ κ hT hmean hκ
      obtain ⟨Y', hY'⟩ := hroots mk₂ hmk₂
      obtain ⟨t, ht, hmove⟩ := hY mk₂ hmk₂ hover Y' hY'
      obtain ⟨v0, hv0, hev⟩ := hshort ℂ halg _ y₂ hy₂
      have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hL _ n
        Dc.hr Dc.eL hrpq hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hθ) hv hκ mk₂ hmk₂ hBm Λ hΛ N hΛ3 Y' hY'
        a _ (hmap a P hP) _ _ v0 hv0
      have hmm : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
          MvPolynomial.map σ P := by
        rw [MvPolynomial.map_map]
        exact congrArg (fun s : c.F →+* ℂ => MvPolynomial.map s P) (RingHom.ext halg)
      rw [hmm, hmove, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx, ← hu] at hval
      refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ * t, by rw [norm_mul, norm_mul, hunit A₂ y₂, hκn, ht]; ring, fun _ => ?_⟩
      have hrd : rdU U f k x = evR Xo c f (unC U k ⟨x, hx⟩) := dif_pos hx
      beta_reduce
      rw [hrd, hev, hval, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx]
      ring)
  refine ⟨C • u • G, sb_smul C huG, fun x hx => ?_⟩
  rw [theta_smul₂ Dc.hr Dc.idx Dc.sympl hn huG hP' hx]
  exact hC () x hx

end GlobalTheory.Dict.ShortRead
