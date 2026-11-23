import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleIndicatorFunctions
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInnerStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacPhase

theorem isMov_one {D : D7} {k : ℕ} (L : Lt D.host.E k) :
    IsMov (1 : Matrix (Fin k) (Fin k) (AfE D)) L L := by
  intro u
  simp only [Matrix.one_mulVec]
  exact ⟨fun h => ⟨u, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩

theorem conjI_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) :
    conjI P ≠ ⊥ := by
  intro h
  apply hP
  rw [eq_bot_iff]
  intro b hb
  have h1 : GlobalTheory.SW.Nbr.co b ∈ conjI P := GlobalTheory.SW.Nbr.mem_conjI.2 (by rwa [GlobalTheory.SW.Nbr.co_co])
  rw [h, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot, ← GlobalTheory.SW.Nbr.co_co b, h1, map_zero]

theorem phase_indep : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∃ ep : ℂ, ‖ep‖ = 1 ∧ ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → om (h, 1) (C.Th (C.xB B) (v₀ L)) = ep • (C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)))) := by
  intro D S T C om hom Lv hn M hidem hM hMm v₀ hv₀ B hB h Λ hh htriv hfg hmov
  obtain ⟨w, hw⟩ : ∃ w : Lt D.host.E T.rank → TF S.rank C.g,
      ∀ L, w L = unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)) := ⟨_, fun _ => rfl⟩
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hΛM : Λ ∈ Vset D.host.E S.rank M := (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M h Λ hM htriv hfg hmov
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := GlobalTheory.SW.stdL_mem_Vset M
  have h6833 := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have fmt_one : ∀ V : HSp D, fmt V 1 = 1 ∧ fmtC V 1 = 1 := fun V =>
    ⟨(((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).1,
      (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).2.1⟩
  obtain ⟨μ, 𝓕, hcov⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).1
  obtain ⟨κ, hκ, hipTh⟩ := GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner D S T C μ 𝓕 hcov
  have hsd : ∀ L ∈ Lv.lats, SelfD C.X (Lv.sh L) := fun L hL => (h6833.2.2.2.1 L hL).1
  have hvac : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens Λ (Lv.sh L)) (w L) := fun L hL => by
    rw [hw L]
    exact GlobalTheory.SW.RecSum.isVac_unitv (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL) (hv₀ L hL)
  have hsbw : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (w L) := fun L hL => (hvac L hL).1
  have hsbv : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (v₀ L) := fun L hL => (hv₀ L hL).1
  have hS1 : ∀ Λ₀ : Lt D.host.E S.rank, IsMov (fmtC S 1) Λ₀ Λ₀ := fun Λ₀ => by
    rw [(fmt_one S).2]
    exact GlobalTheory.Ker.VacPhase.isMov_one Λ₀

  have phase : ∀ L ∈ Lv.lats, ∃ c : ℂ, ‖c‖ = 1 ∧
      om (h, 1) (C.Th (C.xB B) (v₀ L)) = c • C.Th (C.xB B) (w L) := fun L hL =>
    GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hΛM _ _ (hsd L hL) (hsd L hL)
      h hh 1 (one_mem _) hmov (by rw [(fmt_one T).1]; exact GlobalTheory.Ker.VacPhase.isMov_one _)
      (v₀ L) (w L) (hv₀ L hL) (hvac L hL) B hB

  have pos : ∀ L ∈ Lv.lats, GlobalTheory.SW.ip (v₀ L) (w L) ≠ 0 ∧
      GlobalTheory.SW.ip (v₀ L) (w L) = ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) := by
    intro L hL
    obtain ⟨hne, heq⟩ := GlobalTheory.SW.RecSum.unitv_proj (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL)
      (hv₀ L hL) (hvac L hL)
    rw [← hw L] at heq
    refine ⟨hne, ?_⟩
    have h1 : GlobalTheory.SW.ip (w L) (w L) = 1 := (hvac L hL).2.1
    have e : (GlobalTheory.SW.ip (v₀ L) (w L) / ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ)) * GlobalTheory.SW.ip (w L) (w L) =
        GlobalTheory.SW.ip (w L) (w L) := by
      rw [← GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), ← heq]
    rw [h1, mul_one] at e
    have hn0 : ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
    exact (div_eq_one_iff_eq hn0).1 e
  have hXl : C.X.Λ ∈ Lv.lats := h6833.1
  obtain ⟨ep, hep1, hep⟩ := phase C.X.Λ hXl
  refine ⟨ep, hep1, ?_⟩
  intro g L hg hgtriv hLfg hgmov
  rw [← hw L]
  have hL : L ∈ Lv.lats := ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hLfg hgmov).2.1 hgtriv
  obtain ⟨c, hc1, hc⟩ := phase L hL
  rw [hc]

  have hXsd : SelfD C.X C.X.Λ := (show SelfD C.X C.X.Λ ∧ _ from hXl).1
  have hXfs : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨hXsd.1, (h6833.2.2.2.1 _ hXl).2.1⟩
  have hinv : fmt T g * fmt T g⁻¹ = 1 := by
    rw [← (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1 g g⁻¹).2.1, mul_inv_cancel, (fmt_one T).1]
  have hshmov : IsMov (fmt T g) (Lv.sh C.X.Λ) (Lv.sh L) :=
    ((((GlobalTheory.T.finiteAdelicLatticeTransport_laws D T.rank C.X.Λ hXfs).2.2.2 (fmt T g) (fmt T g⁻¹) hinv).2 L hLfg hgmov).2.2.2.2
      Lv.𝔪 (conjI Lv.𝔪) Lv.ne_bot (GlobalTheory.Ker.VacPhase.conjI_ne_bot Lv.ne_bot)).2.1

  obtain ⟨a, ha1, ha⟩ := GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hstd _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (v₀ C.X.Λ) (v₀ L) (hv₀ _ hXl) (hv₀ L hL) B hB
  obtain ⟨b, hb1, hb⟩ := GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hΛM _ hΛM _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (w C.X.Λ) (w L) (hvac _ hXl) (hvac L hL) B hB

  have hThX := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ (hsbv _ hXl)).1.1
  have hThwX := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ (hsbw _ hXl)).1.1
  have hinvar := (((GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).2 μ 𝓕 hcov _ hThX).2.2.2 _ hThwX).2.2.2.2.2
    om hom (1, g)
  rw [ha, hb, ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbv L hL)).2.1 a,
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 b,
    hipTh B hB _ _ (GlobalTheory.SW.TensVac.sb_smul a (hsbv L hL)) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    hipTh B hB _ _ (hsbv _ hXl) (hsbw _ hXl),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbv L hL) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    GlobalTheory.SW.TensVac.ip_smul_right _ (hsbv L hL) (hsbw L hL)] at hinvar
  have e1 : a * (conj b * GlobalTheory.SW.ip (v₀ L) (w L)) = GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ) :=
    mul_left_cancel₀ hκ hinvar
  obtain ⟨hpL0, hpL⟩ := pos L hL
  obtain ⟨-, hpX⟩ := pos _ hXl
  have hnorm : ‖GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ)‖ = ‖GlobalTheory.SW.ip (v₀ L) (w L)‖ := by
    rw [← e1, norm_mul, norm_mul, Complex.norm_conj, ha1, hb1, one_mul, one_mul]
  have e2 : (a * conj b) * GlobalTheory.SW.ip (v₀ L) (w L) = 1 * GlobalTheory.SW.ip (v₀ L) (w L) := by
    rw [mul_assoc, e1, one_mul, hpX, hnorm, ← hpL]
  have hab : a * conj b = 1 := mul_right_cancel₀ hpL0 e2
  have hbb : b * conj b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    norm_num
  have hab' : a = b := by
    calc a = a * (b * conj b) := by rw [hbb, mul_one]
      _ = (a * conj b) * b := by ring
      _ = b := by rw [hab, one_mul]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha1
    exact zero_ne_one ha1

  have hsq : om (h, 1) (om (1, g) (C.Th (C.xB B) (v₀ C.X.Λ))) =
      om (1, g) (om (h, 1) (C.Th (C.xB B) (v₀ C.X.Λ))) := by
    have e : ((h, 1) : GA D S × GA D T) * (1, g) = (1, g) * (h, 1) := by simp
    have := congrArg (fun p => om p (C.Th (C.xB B) (v₀ C.X.Λ))) e
    simpa only [map_mul, Module.End.mul_apply] using this
  rw [ha, hep, map_smul, map_smul, hc, hb, smul_smul, smul_smul,
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 (a * c),
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 (ep * b)] at hsq
  have hfun := ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (GlobalTheory.SW.TensVac.sb_smul (a * c) (hsbw L hL))).1 _
    (GlobalTheory.SW.TensVac.sb_smul (ep * b) (hsbw L hL))).2 hsq
  have e3 := congrArg (fun φ => GlobalTheory.SW.ip φ (w L)) hfun
  rw [GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), (hvac L hL).2.1, mul_one, mul_one,
    hab', mul_comm ep b] at e3
  rw [mul_left_cancel₀ (hab' ▸ ha0) e3]

end GlobalTheory.Ker.VacPhase
