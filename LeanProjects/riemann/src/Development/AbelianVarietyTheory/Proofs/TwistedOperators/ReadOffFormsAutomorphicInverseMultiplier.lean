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
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFockStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBoundStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AutRead

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * (mat y τ * mat b τ) =
    (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * mat y τ * mat b τ
  rw [Matrix.mul_assoc]

theorem ip_smul_self {n g : ℕ} (t : ℂ) {v : TF n g} (hv : SW.IsSB v) :
    SW.ip (t • v) (t • v) = (t * conj t) * SW.ip v v := by
  have hc : SW.IsSB (fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hv hv).2.2.2.1
  have hP : SW.IsSB (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v _ hv hc).2.2.1
  have e : (fun x : Matrix (Fin n) (Fin g) ℚ => (t • v) x * conj ((t • v) x)) = (t * conj t) • (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  rw [SW.ip, SW.ip, e, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hP hP).2.2.2.2.2.1]
  rfl

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem std_mem_Vset {D : D7} {S T : HSp D} (C : Ctx S T) (M : ℕ) (hM : 0 < M) :
    stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := by
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  exact (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M 1 _ hM (Red.trivAt_one _ _) (Red.stdL_fg _) hs1

theorem wG_phi_std {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ)
    (hμ : ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L))
    (γ : GL (Fin T.rank) D.host.E) (hγ : γ ∈ Lv.grp) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    wG C.X C.bas C.idx γ (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      μ γ L • Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank) := by
  obtain ⟨-, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have e1 := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  obtain ⟨-, -, hw3, -⟩ := GlobalTheory.T.weil_action_preserves_theta_and_inner_product D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even γ hun (v₀ L) (hv L hL).1
  have hip := (hw3 (v₀ L) (hv L hL).1).1
  rw [e1, ip_smul_self _ (hv _ hL').1, (hv _ hL').2.1, (hv L hL).2.1, mul_one, Complex.mul_conj] at hip
  have hn1 : ‖μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : Complex.normSq (μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) = 1 := by exact_mod_cast hip
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  rw [(GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    (std_mem_Vset C M hM)).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ hn1 e1, mul_inv_cancel_right₀ (Units.ne_zero _)]

theorem th_phi_ne {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (B : C.Bas) (hB : C.IsB B) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) ≠ 0 := by
  intro h0
  have hstd := std_mem_Vset C M hM
  have hx := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hsb := (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ hsb
  have hsb0 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ hsb hsb).2.1 0
  have e : C.Th (C.xB B) ((0 : ℂ) • Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
    rw [h2, zero_smul, h0]
  have hΦ0 : Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank) = 0 := by
    rw [(h1 _ hsb0).2 e.symm, zero_smul]
  have hip := (GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  rw [hΦ0, SW.ip] at hip
  have ez : (fun x : Matrix (Fin S.rank) (Fin C.g) ℚ => (0 : TF S.rank C.g) x * conj ((0 : TF S.rank C.g) x)) =
      (0 : ℂ) • (0 : TF S.rank C.g) := by
    funext x; simp
  rw [ez, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ SW.isSB_zero SW.isSB_zero).2.2.2.2.2.1, zero_mul] at hip
  haveI : Finite (𝓞 D.host.E ⧸ Lv.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ Lv.ne_bot
  have hpos : 0 < Nat.card Lv.J := Nat.card_pos
  exact (Nat.cast_ne_zero.2 hpos.ne') hip.symm

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem read_off_automorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hφQ hK v₀ μ hv hμ ep cf hep gL hgL F hFhol hFb hFφ
    γ hγ L hL
  obtain ⟨hΛl, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k0, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hmv := (hJ B hB).2.2.2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.rational_unitary_group_structure D S T C).1
  have hγA : IsRatOf T γ (e ⟨γ, hun⟩).1 := he ⟨γ, hun⟩
  have hγAQ : (e ⟨γ, hun⟩).1 ∈ GQ T := (e ⟨γ, hun⟩).2
  have hgrpT := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T
  have hcomm := hgrpT.2.2.2.1
  obtain ⟨a₀, ha₀, f, hf, hγAe⟩ := hgrpT.2.2.1 (e ⟨γ, hun⟩).1
  set γA := (e ⟨γ, hun⟩).1 with hγAdef
  obtain ⟨g1f, g1t, g1m⟩ := hgL L hL
  obtain ⟨g2f, g2t, g2m⟩ := hgL (mapL γ L) hL'
  have hk := GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup D S T C Lv γ ⟨k0, hkJ⟩ hred a₀ f (gL L) (gL (mapL γ L)) L ha₀ hf (hγAe ▸ hγA) g1f g2f g1t g2t
    hL.1.1 (hlat L hL).2.1 hL'.1.1 g1m g2m
  set k := (gL (mapL γ L))⁻¹ * f * gL L with hkdef

  have hstd := std_mem_Vset C M hM
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  obtain ⟨hbase0, hu⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase _ (hv _ hΛl)
  have hk0 : om (1, k) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    have h1 := (hK k ⟨k0, hkJ⟩ hk).1
    rw [hft, hu t, map_smul] at h1
    exact smul_right_injective _ ht0 h1

  have hsb : ∀ L₁ ∈ Lv.lats, SW.IsSB (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := fun L₁ hL₁ =>
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L₁ hL₁ _ hstd).1
  have hep1 : ∀ L₁ ∈ Lv.lats, ‖ep 1‖ = 1 ∧ ‖cf (gL L₁)‖ = 1 ∧ om (1, gL L₁)
      (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      (ep 1 * cf (gL L₁)) • C.Th (C.xB B) (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := by
    intro L₁ hL₁
    obtain ⟨h1, h2, h3⟩ := hgL L₁ hL₁
    have := hep 1 _ (gL L₁) L₁ (one_mem _) (Red.trivAt_one _ _) (Red.stdL_fg _) hs1 h1 h2 hL₁.1.1 h3
    simpa only [Prod.mk_one_one] using this
  have key : ∀ a ∈ GinfC T, F (mapL γ L) (lact γ (C.xB (C.mvB a B))) = (μ γ L)⁻¹ * F L (C.xB (C.mvB a B)) := by
    intro a ha
    have hBa : C.IsB (C.mvB a B) := (hmv a).1
    have ha₀a : a₀ * a ∈ GinfC T := mul_mem ha₀ ha
    have hY : lact γ (C.xB (C.mvB a B)) = C.xB (C.mvB (a₀ * a) B) := by
      rw [← ((hJ _ hBa).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA, hγAe, mul_assoc,
        ← (hcomm a ha).2.2 f hf, ← mul_assoc, (hmv f).2.1 (a₀ * a), (hmv f).2.2.1 hf]

    have hel : γA * (gL L * a) = gL (mapL γ L) * (a₀ * a) * k := by
      have c1 : a₀ * a * (gL (mapL γ L))⁻¹ = (gL (mapL γ L))⁻¹ * (a₀ * a) := (hcomm _ ha₀a).2.2 _ (inv_mem g2f)
      have c2 : a * f = f * a := (hcomm a ha).2.2 f hf
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      rw [hkdef, hγAe]
      calc a₀ * f * (gL L * a) = a₀ * (f * a) * gL L := by rw [← c3]; group
        _ = gL (mapL γ L) * (a₀ * a * (gL (mapL γ L))⁻¹) * f * gL L := by rw [c1, ← c2]; group
        _ = _ := by group
    have s1 : φ (gL L * a) = φ (gL (mapL γ L) * (a₀ * a)) := by
      rw [← hφQ γA hγAQ, hel, (hK k ⟨k0, hkJ⟩ hk).2]
    rw [hFφ L hL a ha, hFφ (mapL γ L) hL' _ ha₀a] at s1

    have hne : C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) ≠ 0 :=
      th_phi_ne C Lv hn M hM hM𝔪 v₀ hv _ (hmv _).1 _ hL'
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ hBa).2.1
    have hX1 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL L) * z a * μ γ L) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, γA) * ((1, a) * (1, gL L)) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_assoc]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hep1 L hL).2.2, map_smul,
        hz a ha _ (hsb L hL), map_smul, map_smul, ((GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock D S T C om hW).2 γ γA hγA _ (hsb L hL)).1 _ hx,
        wG_phi_std C Lv hn M hM hM𝔪 v₀ hv μ hμ γ hγ L hL, hY,
        (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ ((hJ _ (hmv _).1).2.1) _ (hsb _ hL')).2.1, smul_smul, smul_smul]
    have hX2 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL (mapL γ L)) * z (a₀ * a)) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, a₀ * a) * ((1, gL (mapL γ L)) * (1, k)) := by
        have eq : γA * a * gL L = a₀ * a * (gL (mapL γ L) * k) := by
          rw [mul_assoc γA, c3, hel, ← mul_assoc (a₀ * a), ← (hcomm _ ha₀a).2.2 _ g2f]
        rw [eq]
        simp only [Prod.mk_mul_mk, one_mul]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk0, (hep1 _ hL').2.2, map_smul,
        hz _ ha₀a _ (hsb _ hL'), smul_smul]
    have hsc : ep 1 * cf (gL L) * z a * μ γ L = ep 1 * cf (gL (mapL γ L)) * z (a₀ * a) :=
      smul_left_injective ℂ hne (hX1.symm.trans hX2)

    have hza : z a ≠ 0 := by
      intro h0
      have h1 := hz a ha _ (hsb L hL)
      rw [h0, zero_smul] at h1
      have h2 : om (1, a⁻¹) (om (1, a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)))) =
          C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [h1, map_zero] at h2
      exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB L hL h2.symm
    have hep0 : ep 1 ≠ 0 := fun h0 => by
      have := (hep1 L hL).1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hcf0 : cf (gL L) ≠ 0 := fun h0 => by
      have := (hep1 L hL).2.1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hμ0 : μ γ L ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hsc
      have hcf1 : cf (gL (mapL γ L)) ≠ 0 := fun h1 => by
        have := (hep1 _ hL').2.1; rw [h1, norm_zero] at this; exact zero_ne_one this
      have hz1 : z (a₀ * a) ≠ 0 := by
        intro h1
        have h3 := hz _ ha₀a _ (hsb _ hL')
        rw [h1, zero_smul] at h3
        have h2 : om (1, (a₀ * a)⁻¹) (om (1, a₀ * a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)))) =
            C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
            Module.End.one_apply]
        rw [h3, map_zero] at h2
        exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB _ hL' h2.symm
      exact mul_ne_zero (mul_ne_zero hep0 hcf1) hz1 hsc.symm
    rw [hY]
    have hinv : μ γ L * (μ γ L)⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have hq : z a * ep 1 * cf (gL L) * μ γ L ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hza hep0) hcf0) hμ0
    apply mul_left_cancel₀ hq
    linear_combination (F (mapL γ L) (C.xB (C.mvB (a₀ * a) B))) * hsc - s1 -
      (z a * ep 1 * cf (gL L) * F L (C.xB (C.mvB a B))) * hinv
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.T.domain_frame_eq_real_translate_mul_borel D S T C B hB x hx
  have hxa : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ (hmv a).1).2.1
  have hya : lact γ (C.xB (C.mvB a B)) ∈ C.X.dom := by
    rw [← ((hJ _ (hmv a).1).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA]
    exact (hJ _ (hmv _).1).2.1
  rw [lact_rmul, hFb _ hL' _ hya b hb, hFb L hL _ hxa b hb, key a ha]
  ring

end GlobalTheory.Ker.AutRead
