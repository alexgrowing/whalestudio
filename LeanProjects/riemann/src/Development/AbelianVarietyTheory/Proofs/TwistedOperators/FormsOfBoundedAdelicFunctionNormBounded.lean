import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.BddForms

theorem fg_of_mem_lats {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    (Lv : SW.Level X) {L : Lt E r} (hL : L ∈ Lv.lats) : L.FG := by
  obtain ⟨-, s, hcop, hs, -⟩ := hL
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hcop
    have hle := Ideal.mul_le_left (I := Lv.𝔪) (J := conjI Lv.𝔪)
    rw [hcop] at hle
    exact Lv.proper (top_le_iff.1 hle)
  let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := s • LinearMap.id
  have hinj : Function.Injective f := fun v w h => smul_right_injective _ hs0 h
  have hle : L.map f ≤ X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hs v hv
  have : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
  exact Submodule.fg_of_fg_map_injective f hinj (isNoetherian_submodule.1 this _ hle)

theorem zpow_mul_rpow_sq (t : ℝ) (ht : 0 < t) (l : ℤ) : t ^ l * (t ^ 2) ^ (-(l : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
    Real.rpow_intCast]
  exact mul_inv_cancel₀ (zpow_ne_zero _ ht.ne')

theorem diag_ne_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  obtain ⟨hdet, hlow⟩ := hb τ
  have htri : (mat b τ).BlockTriangular id := fun a c hca => hlow a c hca
  rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)

theorem exists_isSB_ne (n g : ℕ) : ∃ φ : TF n g, SW.IsSB φ ∧ φ ≠ 0 := by
  have key : ∀ x y : Matrix (Fin n) (Fin g) ℚ, SW.IntM y → (SW.IntM (x + y) ↔ SW.IntM x) := by
    intro x y hy
    constructor
    · intro h k i
      simpa using (h k i).sub (hy k i)
    · intro h k i
      simpa using (h k i).add (hy k i)
  have h0 : SW.IntM (0 : Matrix (Fin n) (Fin g) ℚ) := fun k i => by
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℚ))
  refine ⟨fun x => if SW.IntM x then 1 else 0, ⟨1, one_pos, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : SW.IntM x
    · simpa using h
    · simp [h] at hx
  · intro x y hy
    simp only [Nat.cast_one, one_smul, key x y hy]
  · intro h
    have := congrFun h 0
    simp [h0] at this

end GlobalTheory.AdSpan.BddForms

namespace GlobalTheory.AdSpan.BddForms

theorem pnorm_le_of_bdd : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  intro D S T C om hW Lv hn M hw hM hMm B hB f' _hbase c c' z φ hz _hγ _hk v₀ μ _hvac _hμ ep cf hepcf gL hgL F
    _hFd hFb hFφ hφb
  obtain ⟨K, hKφ⟩ := hφb
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hmv : ∀ a, C.IsB (C.mvB a B) := fun a => ((hJ B hB).2.2.2.2.2 a).1
  have hdom : ∀ a, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hJ _ (hmv a)).2.1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isSB_ne S.rank C.g

  have hz1 : ∀ a ∈ GinfC T, ‖z a‖ = 1 := by
    intro a ha
    obtain ⟨c0, hc0, hc0'⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hW 1 (one_mem _) a ha B hB
    have e1 : om (1, a) (C.Th (C.xB B) φ₀) = z a • C.Th (C.xB (C.mvB a B)) φ₀ := hz a ha φ₀ hφ₀
    have e2 := hc0' φ₀ hφ₀
    have : z a = c0 := RealChar.smul_cancel (RealChar.th_ne C (hdom a) hφ₀ hφ₀ne) (e1.symm.trans e2)
    rw [this, hc0]

  have hstdFG : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hec : ∀ L ∈ Lv.lats, ‖ep 1 * cf (gL L)‖ = 1 := by
    intro L hL
    obtain ⟨h1, h2, h3⟩ := hgL L hL
    obtain ⟨e1, e2, -⟩ := hepcf 1 (stdL _ _) (gL L) L (one_mem _) (Red.trivAt_one _ _) hstdFG
      (by rw [Red.fmtC_one]; exact Red.isMov_one _) h1 h2 (fg_of_mem_lats Lv hL) h3
    rw [norm_mul, e1, e2, one_mul]

  have hFa : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, ‖F L (C.xB (C.mvB a B))‖ ≤ K := by
    intro L hL a ha
    have h := hKφ (gL L * a)
    rw [hFφ L hL a ha, norm_mul, norm_mul, hz1 a ha, hec L hL, one_mul, one_mul] at h
    exact h
  refine ⟨K, fun L hL x hx => ?_⟩
  obtain ⟨hON, hbB, hxe, hdm, -⟩ := hob x hx
  obtain ⟨a, ha, hax⟩ := (GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB).2.1 (o x) hON
  have hox : o x ∈ C.X.dom := hax ▸ hdom a
  have hFo : ‖F L (o x)‖ ≤ K := hax ▸ hFa L hL a ha
  set la := wtOf C.X C.hr c c' S.rank with hla
  have hval : F L x = bchar la (b x) * F L (o x) := by
    have := hFb L hL (o x) hox (b x) hbB
    rw [← hxe] at this
    exact this
  have hprod : ‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    simp_rw [norm_prod, norm_zpow]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    exact zpow_mul_rpow_sq _ (norm_pos_iff.2 (diag_ne_zero hbB τ i)) _
  simp only [Data.pnorm]
  simp only [← hdm]
  rw [hval, norm_mul]
  calc ‖bchar la (b x)‖ * ‖F L (o x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)
      = ‖F L (o x)‖ * (‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)) := by ring
    _ = ‖F L (o x)‖ := by rw [hprod, mul_one]
    _ ≤ K := hFo

end GlobalTheory.AdSpan.BddForms
