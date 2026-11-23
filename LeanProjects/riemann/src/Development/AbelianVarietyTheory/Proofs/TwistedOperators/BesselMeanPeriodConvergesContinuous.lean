import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.BesMean

theorem continuous_integral_of_le {P X : Type} [TopologicalSpace P] [FirstCountableTopology P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {T : P → X → ℂ}
    (hT : Continuous fun q : P × X => T q.1 q.2) {b : P → ℝ} (hb : Continuous b) (hle : ∀ p x, ‖T p x‖ ≤ b p) :
    Continuous fun p => ∫ x, T p x ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine continuousAt_of_dominated (bound := fun _ => b p₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun p => (hT.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hb.continuousAt.eventually (gt_mem_nhds (lt_add_one (b p₀)))] with p hp
    exact .of_forall fun x => (hle p x).trans hp.le
  · exact .of_forall fun x => (hT.comp (continuous_id.prodMk continuous_const)).continuousAt

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem ptT_rat {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) {n : GA D T}
    (hn : n ∈ GQ T) : ptT d S (yZero S ρ z) n ∈ ratMx D T₀.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    refine neg_mem ⟨vecMulVec z fun i : Fin ρ => if i.1 + 1 = ρ then 1 else 0, ?_⟩
    ext i j
    change incA D (z i * if j.1 + 1 = ρ then 1 else 0) = incA D (z i) * ell D ρ j
    rw [map_mul, ell]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn))
    (ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))))

theorem heisO_zero_pt (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) : heisO ψ S T w f 0 = f w := by
  rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

variable {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J) {Φ : WO B.V J.W → ℂ}

def ker (Φ : WO B.V J.W → ℂ) (h₀ : GA D B.A) (g : GA D J.W) : ℂ := flBF s (s.om (embA B.d B.o h₀, g) Φ) 0

theorem ker_val (hΦ : IsThetaFunO ψ B.V J.W Φ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d)
    (h' : GA D J.W₀) (h : GA D J.W) :
    ker s Φ h₀ (n * J.d.emb0 h' * h) =
      star (psiFlag ψ J.d n) * fjKer ψ J.d B.o B.ζ s.om₀ (flBF s (s.om (1, h) Φ)) h₀ n h' := by
  have e : s.om (embA B.d B.o h₀, n * J.d.emb0 h' * h) Φ = s.om (embA B.d B.o h₀, n * J.d.emb0 h') (s.om (1, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ (s.weil.om_pres _ _ hΦ) h₀ n hn h']
  rfl

theorem theta_flBF (hΦ : IsThetaFunO ψ B.V J.W Φ) : IsThetaFunO ψ B.V₀ J.W₀ (flBF s Φ) := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have h := (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hb.1
    (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ hΦ).2
  rw [← hx] at h
  exact h

theorem ker_left (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h₀ : GA D B.A) (g : GA D J.W) :
    ‖ker s Φ (γ * h₀) g‖ = ‖ker s Φ h₀ g‖ := by
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, g) _ hΦ
  have hΞ := theta_flBF s hΨ
  have e : s.om (embA B.d B.o (γ * h₀), g) Φ =
      s.om (embA B.d B.o γ, 1 * J.d.emb0 1) (s.om (embA B.d B.o h₀, g) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, map_one, one_mul, one_mul, map_mul (embA B.d B.o)]
  have e1 : ((1, 1) : GA D B.V₀ × GA D J.W₀) = 1 := rfl
  have hp : ‖star (psiFlag ψ J.d 1)‖ = 1 := by rw [norm_star]; exact s.weil.std.1.2.1 _
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ hΨ γ 1 (one_mem _) 1, opA, jacT_one, e1, map_one,
    Module.End.one_apply, id, Pi.smul_apply, smul_eq_mul, norm_mul, hp, one_mul,
    s.weil₀.om_aut _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ hΞ]
  rfl

theorem ker_right (hΦ : IsThetaFunO ψ B.V J.W Φ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d) (hnq : n ∈ GQ J.W)
    {h' : GA D J.W₀} (hhq : h' ∈ GQ J.W₀) (g : GA D J.W) :
    ‖ker s Φ h₀ (n * J.d.emb0 h' * g)‖ = ‖ker s Φ h₀ g‖ := by
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, g) _ hΦ
  have hΞ := theta_flBF s hΨ
  have e : s.om (embA B.d B.o h₀, n * J.d.emb0 h' * g) Φ =
      s.om (embA B.d B.o 1, n * J.d.emb0 h') (s.om (embA B.d B.o h₀, g) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, map_one, one_mul]
  have e2 : ((B.o.emb (1, 1), 1) : GA D B.V₀ × GA D J.W₀) = 1 := by
    rw [show ((1, 1) : GA D B.A × GA D B.L) = 1 from rfl, map_one]; rfl
  obtain ⟨δ, hδ⟩ := ptT_rat J.d B.V₀ (vecB B.o B.ζ) hnq
  have hψ := s.weil.std.1.2.1
  have hp : ‖star (psiFlag ψ J.d n)‖ = 1 := by rw [norm_star]; exact hψ _
  have h2 := (s.weil₀.om_pres (1, h') _ hΞ).quasi δ 0
  rw [add_zero, s.weil₀.om_aut 1 (one_mem _) h' hhq _ hΞ] at h2
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ hΨ 1 n hn h', e2, map_one, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul, norm_mul, hp, one_mul, opA, jacT, Pi.smul_apply, heisO_zero_pt, ← hδ, smul_eq_mul,
    norm_mul, hψ, one_mul]
  refine (congrArg norm h2).trans ?_
  rw [norm_mul, hψ, one_mul]
  rfl

theorem continuous_ker (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Continuous fun p : GA D J.W × GA D B.A => ker s Φ p.2 p.1 := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hemb : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have h2 := GlobalTheory.FlatCont.flatAt_om_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
  rw [← hx] at h2
  have h3 : Continuous fun p : GA D J.W × GA D B.A =>
      (((embA B.d B.o p.2, p.1), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
        (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
    ((hemb.comp continuous_snd).prodMk continuous_fst).prodMk continuous_const
  have h4 := h2.comp h3
  simp only [Function.comp_def] at h4
  simp only [ker, flBF, flatS]
  exact h4

theorem ker_le (hΦ : IsThetaFunO ψ B.V J.W Φ) : ∃ (C : ℝ) (a b : ℕ), 0 ≤ C ∧ ∀ h₀ g,
    ‖ker s Φ h₀ g‖ ≤ C * quotHeight B.A h₀ ^ a * height J.W g ^ b := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s J.d.e hb.1 Φ hΦ
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ ρ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  rw [← hx] at hC₁
  refine ⟨|C₁| * (|C₄| * (|C₅| * 2 ^ a₅)) ^ A₁, a₅ * A₁, A₁, by positivity, fun h₀ g => ?_⟩
  obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight B.A h₀
  rw [← ker_left s hΦ hγ]
  have p1 := height_pos B.A (γ * h₀)
  have p2 := height_pos J.W g
  have p3 := height_pos B.V (embA B.d B.o (γ * h₀))
  have p4 := height_pos B.V₀ (B.o.emb (γ * h₀, 1))
  have q0 := quotHeight_pos B.A h₀
  have f1 : height B.V (embA B.d B.o (γ * h₀)) ≤ |C₄| * (|C₅| * (2 * quotHeight B.A h₀) ^ a₅) := by
    refine (hC₄ _).trans (mul_le_mul (le_abs_self _) ((hC₅ _).trans ?_) p4.le (abs_nonneg _))
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ p1.le e1 _) (pow_pos p1 _).le (abs_nonneg _)
  calc _ ≤ C₁ * (height B.V (embA B.d B.o (γ * h₀)) * height J.W g) ^ A₁ := hC₁ _ _ _ _
    _ ≤ |C₁| * (|C₄| * (|C₅| * (2 * quotHeight B.A h₀) ^ a₅) * height J.W g) ^ A₁ :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_pos p3 p2).le (mul_le_mul_of_nonneg_right f1 p2.le) _)
          (pow_pos (mul_pos p3 p2) _).le (abs_nonneg _)
    _ = _ := by simp only [mul_pow, pow_mul]; ring

theorem ker_le_quot (hΦ : IsThetaFunO ψ B.V J.W Φ) : ∃ (C : ℝ) (a b : ℕ), 0 ≤ C ∧ ∀ h₀, ∀ n ∈ flagN J.d, ∀ h' h,
    ‖ker s Φ h₀ (n * J.d.emb0 h' * h)‖ ≤ C * quotHeight B.A h₀ ^ a * (quotHeight J.W₀ h' * height J.W h) ^ b := by
  obtain ⟨C, a, b, hC0, hC⟩ := ker_le s hΦ
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ ρ J.d
  obtain ⟨KN, hKN, cN⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)).1
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact J.W (hKN.image continuous_subtype_val)
  refine ⟨C * (|M| * (|C₃| * 2)) ^ b, a, b, by positivity, fun h₀ n hn h' h => ?_⟩
  obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight J.W₀ h'
  obtain ⟨δ, hδ, m, hm, e⟩ := cN ⟨J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹, GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D J.W J.W₀ ρ J.d n hn γ⟩
  have e' : J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹ = δ.1 * m.1 := congrArg Subtype.val e
  have e2 : 1 * J.d.emb0 γ * (n * J.d.emb0 h' * h) = δ.1 * J.d.emb0 1 * (m.1 * J.d.emb0 (γ * h') * h) := by
    rw [map_mul, map_one]
    calc 1 * J.d.emb0 γ * (n * J.d.emb0 h' * h)
        = (J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹) * (J.d.emb0 γ * J.d.emb0 h') * h := by group
      _ = _ := by rw [e']; group
  rw [← ker_right s hΦ h₀ (one_mem _) (one_mem _) hγ, e2, ker_right s hΦ h₀ δ.2 hδ (one_mem _)]
  have p1 := height_pos J.W₀ (γ * h')
  have p2 := height_pos J.W h
  have p3 := height_pos J.W (J.d.emb0 (γ * h'))
  have q0 := quotHeight_pos B.A h₀
  have q1 := quotHeight_pos J.W₀ h'
  have f1 : height J.W (m.1 * J.d.emb0 (γ * h') * h) ≤ |M| * (|C₃| * (2 * quotHeight J.W₀ h')) * height J.W h := by
    refine (height_mul_le _ _ _).trans (mul_le_mul_of_nonneg_right ((height_mul_le _ _ _).trans ?_) p2.le)
    exact mul_le_mul ((hM _ ⟨m, hm, rfl⟩).trans (le_abs_self _))
      ((hC₃ _).trans (mul_le_mul (le_abs_self _) e1 p1.le (abs_nonneg _))) p3.le (abs_nonneg _)
  calc _ ≤ C * quotHeight B.A h₀ ^ a * height J.W (m.1 * J.d.emb0 (γ * h') * h) ^ b := hC _ _
    _ ≤ C * quotHeight B.A h₀ ^ a * (|M| * (|C₃| * (2 * quotHeight J.W₀ h')) * height J.W h) ^ b :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _ _).le f1 _) (by positivity)
    _ = _ := by simp only [mul_pow]; ring

def inner (φ : GA D B.A → ℂ) (Φ : WO B.V J.W → ℂ) (g : GA D J.W) : ℂ := ∫ h₀ in B.vA.𝓕, φ h₀ * ker s Φ h₀ g ∂B.vA.μ

theorem norm_mul_le_of_decay {z w : ℂ} {q C c y : ℝ} (hC : 0 ≤ C) (hy : 0 ≤ y) (hz : ‖z‖ * q ≤ c) (hw : ‖w‖ ≤ C * q * y) :
    ‖z * w‖ ≤ c * C * y := by
  calc ‖z * w‖ = ‖z‖ * ‖w‖ := norm_mul _ _
    _ ≤ ‖z‖ * (C * q * y) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖z‖ * q * (C * y) := by ring
    _ ≤ c * (C * y) := mul_le_mul_of_nonneg_right hz (mul_nonneg hC hy)
    _ = _ := by ring

variable {φ : GA D B.A → ℂ} {G : GA D J.W → ℂ}

theorem inner_law (hφ : RapidDec B.A φ) (hΦ : IsThetaFunO ψ B.V J.W Φ) : Continuous (inner s φ Φ) ∧
    ∃ (C : ℝ) (b : ℕ), 0 ≤ C ∧ ∀ n ∈ flagN J.d, ∀ h' h,
      ‖inner s φ Φ (n * J.d.emb0 h' * h)‖ ≤ C * (quotHeight J.W₀ h' * height J.W h) ^ b := by
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  constructor
  · obtain ⟨C, a, b, hC0, hC⟩ := ker_le s hΦ
    obtain ⟨c, hc⟩ := hφ.decay a
    exact continuous_integral_of_le (B.vA.μ.restrict B.vA.𝓕) (T := fun g h₀ => φ h₀ * ker s Φ h₀ g)
      ((hφ.continuous.comp continuous_snd).mul (continuous_ker s hΦ)) (b := fun g => c * C * height J.W g ^ b)
      (continuous_const.mul ((continuous_height J.W).pow b))
      fun g h₀ => norm_mul_le_of_decay hC0 (pow_pos (height_pos _ _) _).le (hc h₀) (hC h₀ g)
  · obtain ⟨C, a, b, hC0, hC⟩ := ker_le_quot s hΦ
    obtain ⟨c, hc⟩ := hφ.decay a
    refine ⟨|c| * C * (B.vA.μ B.vA.𝓕).toReal, b, by positivity, fun n hn h' h => ?_⟩
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ =>
      norm_mul_le_of_decay hC0 (pow_pos (mul_pos (quotHeight_pos _ h') (height_pos _ h)) b).le
        ((hc h₀).trans (le_abs_self c)) (hC h₀ n hn h' h)
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring

theorem fjAllFun_eq (hΦ : IsThetaFunO ψ B.V J.W Φ) (h : GA D J.W) (h' : GA D J.W₀) (n : flagN J.d) :
    fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)) h' n =
      G (n.1 * J.d.emb0 h' * h) * inner s φ Φ (n.1 * J.d.emb0 h' * h) := by
  rw [fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _), inner]
  simp only [ker_val s hΦ _ n.2, mul_left_comm (φ _)]

theorem perAll_flBF_cont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)))) ∧ Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := by
  intro D ψ ρ B J s φ G Φ hφ hG hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨hIc, C, b, hC0, hI⟩ := inner_law s hφ hΦ
  obtain ⟨C₁, a₁, h1⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
  obtain ⟨C₃, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D J.W G hG).2 (a₁ * b)
  obtain ⟨F, hF⟩ : ∃ F : GA D J.W → GA D J.W₀ × flagN J.d → ℂ,
      F = fun h p => G (p.2.1 * J.d.emb0 p.1 * h) * inner s φ Φ (p.2.1 * J.d.emb0 p.1 * h) := ⟨_, rfl⟩
  have hFe : ∀ h, Function.uncurry (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ))) = F h :=
    fun h => by subst hF; exact funext fun p => fjAllFun_eq s hΦ h p.1 p.2
  have hbound : ∀ h p, ‖F h p‖ ≤ C₃ * height J.W h ^ (a₁ * b) * (C * |C₁| ^ b) * height J.W h ^ b := by
    subst hF
    rintro h ⟨h', n⟩
    have ht := height_pos J.W h
    have qg := quotHeight_pos J.W (n.1 * J.d.emb0 h')
    refine norm_mul_le_of_decay (by positivity) (pow_pos ht b).le (h3 (n.1 * J.d.emb0 h') h) ((hI n.1 n.2 h' h).trans ?_)
    have hq : quotHeight J.W₀ h' ≤ |C₁| * quotHeight J.W (n.1 * J.d.emb0 h') ^ a₁ :=
      (h1 n.1 n.2 h').1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg _).le)
    calc _ ≤ C * (|C₁| * quotHeight J.W (n.1 * J.d.emb0 h') ^ a₁ * height J.W h) ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (quotHeight_pos _ _) ht).le
            (mul_le_mul_of_nonneg_right hq ht.le) b) hC0
      _ = _ := by simp only [mul_pow, pow_mul]; ring
  have hcont : Continuous fun q : GA D J.W × (GA D J.W₀ × flagN J.d) => F q.1 q.2 := by
    subst hF
    have hg : Continuous fun q : GA D J.W × (GA D J.W₀ × flagN J.d) => (q.2.2 : GA D J.W) * J.d.emb0 q.2.1 * q.1 :=
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul
        (J.d.continuous_embed.comp (continuous_fst.comp continuous_snd))).mul continuous_fst
    exact (hG.continuous.comp hg).mul (hIc.comp hg)
  have hint : ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝
      (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ))) := by
    intro h
    rw [AbsConv, hFe]
    exact Integrable.of_bound (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable _
      (.of_forall (hbound h))
  refine ⟨hint, ?_⟩
  have heq : ∀ h, J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) =
      ∫ p, F h p ∂((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)) := fun h => by
    rw [← hFe, integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  exact continuous_integral_of_le _ hcont
    (((continuous_const.mul ((continuous_height J.W).pow _)).mul continuous_const).mul ((continuous_height J.W).pow b)) hbound

end GlobalTheory.BesMean

end
