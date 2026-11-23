import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingNegligibleOrbitUnfoldedIntegralEqZeroStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Core.Rk.NegOrbit
open GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

variable {D : D7} (V : HSp D)

def IsNeg (x : GA D (dblSp V)) : Prop := ¬ ∃ δ ∈ GQ V, x * (io V (δ, 1))⁻¹ ∈ siegel V

variable {V}

theorem isNeg_siegel_mul {p x : GA D (dblSp V)} (hp : p ∈ siegel V) : IsNeg V (p * x) ↔ IsNeg V x := by
  unfold IsNeg
  refine not_congr ⟨fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩, fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩⟩
  · have := (siegel V).mul_mem ((siegel V).inv_mem hp) h
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using (siegel V).mul_mem hp h

theorem isNeg_mul_io {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) → IsNeg V x := by
  intro h ⟨δ, hδ, hx⟩
  refine h ⟨γ₂⁻¹ * δ * γ₁, (GQ V).mul_mem ((GQ V).mul_mem ((GQ V).inv_mem h₂) hδ) h₁, ?_⟩
  have e : x * io V (γ₁, γ₂) * (io V (γ₂⁻¹ * δ * γ₁, 1))⁻¹ = x * (io V (δ, 1))⁻¹ * io V (γ₂, γ₂) := by
    simp only [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    ext <;> simp [mul_assoc]
  rw [e]
  exact (siegel V).mul_mem hx ((io_mem_siegel V).2 rfl)

theorem isNeg_mul_io_iff {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) ↔ IsNeg V x := by
  refine ⟨isNeg_mul_io h₁ h₂, fun h => isNeg_mul_io ((GQ V).inv_mem h₁) ((GQ V).inv_mem h₂) ?_⟩
  have e : ((γ₁, γ₂) * (γ₁⁻¹, γ₂⁻¹) : GA D V × GA D V) = 1 := by ext <;> simp
  rw [mul_assoc, ← map_mul, e, map_one, mul_one]
  exact h

theorem exists_out_rmul (q : SiegelCosets V) (g : GQ (dblSp V)) : ∃ p ∈ siegelQ V,
    (((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) = p * (q.out : GQ (dblSp V)) * g := by
  have e : mk ((siegel V).subgroupOf (GQ (dblSp V))) (q.out * g) = mk _ (rmul _ g q).out :=
    ((rmul_mk g q.out).symm.trans (congrArg (rmul _ g) (Quotient.out_eq q))).trans (Quotient.out_eq _).symm
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  refine ⟨((p : GQ (dblSp V)) : GA D (dblSp V)), ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩, ?_⟩
  rw [← hp]
  simp [mul_assoc]

theorem isNeg_out_rmul_iff (q : SiegelCosets V) {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V ((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q).out : GQ (dblSp V)) ↔ IsNeg V (q.out : GQ (dblSp V)) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩
  rw [e, mul_assoc, isNeg_siegel_mul hp.1]
  exact isNeg_mul_io_iff h₁ h₂

theorem apply_out_rmul {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) (q : SiegelCosets V) (g : GQ (dblSp V)) (y : GA D (dblSp V)) :
    φ ((((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ ((q.out : GQ (dblSp V)) * g * y) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q g
  rw [e, mul_assoc, mul_assoc, apply_siegelQ_mul V a hμ hφ hp, mul_assoc]

abbrev NegCosets (V : HSp D) : Type := {q : SiegelCosets V // IsNeg V (q.out : GQ (dblSp V))}

def ioEquiv {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) : NegCosets V ≃ NegCosets V where
  toFun q := ⟨rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1, (isNeg_out_rmul_iff q.1 h₁ h₂).2 q.2⟩
  invFun q := ⟨rmul _ ⟨io V (γ₁⁻¹, γ₂⁻¹), io_mem_GQ V (inv_mem h₁) (inv_mem h₂)⟩ q.1,
    (isNeg_out_rmul_iff q.1 (inv_mem h₁) (inv_mem h₂)).2 q.2⟩
  left_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))
  right_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))

def negAction (V : HSp D) : MulAction (GQ V) (NegCosets V) where
  smul δ q := ioEquiv (inv_mem δ.2) (one_mem (GQ V)) q
  one_smul q := Subtype.ext (by
    show rmul _ _ q.1 = q.1
    convert rmul_one q.1 using 2
    ext1; simp; exact map_one (io V))
  mul_smul δ₁ δ₂ q := Subtype.ext (by
    show rmul _ _ q.1 = rmul _ _ (rmul _ _ q.1)
    rw [← rmul_mul]
    congr 1
    ext1; simp [← map_mul])

attribute [local instance] negAction

@[simp] theorem io_one_one : io V (1, 1) = 1 := map_one (io V)

theorem smul_val (δ : GQ V) (q : NegCosets V) : (δ • q).1 =
    rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ q.1 := rfl

theorem mem_map_stabilizer_iff (y : NegCosets V) (x : GA D V) :
    x ∈ (MulAction.stabilizer (GQ V) y).map (GQ V).subtype ↔
      x ∈ GQ V ∧ ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ siegel V := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ.2, ?_⟩
    obtain ⟨p, hp, e⟩ := exists_out_rmul y.1 ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩
    have hv : rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ y.1 = y.1 :=
      (smul_val δ y).symm.trans (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hδ))
    rw [hv] at e
    have e' : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) =
        p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) := e
    have h' : p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) * io V ((δ : GA D V), 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ = p := by
      rw [mul_assoc (p * _), ← map_mul]
      simp [io_one_one]
    rw [← e'] at h'
    rw [Subgroup.coe_subtype, h']
    exact hp.1
  · rintro ⟨hx, hs⟩
    refine ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_), rfl⟩
    rw [smul_val]
    conv_lhs => rw [← Quotient.out_eq y.1]
    have hr : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ GQ (dblSp V) :=
      mul_mem (mul_mem (y.1.out).2 (io_mem_GQ V hx (one_mem _))) (inv_mem (y.1.out).2)
    refine ((rmul_mk _ _).trans (mk_eq_iff.2 ⟨⟨⟨_, hr⟩, Subgroup.mem_subgroupOf.2 hs⟩, ?_⟩)).trans (Quotient.out_eq _)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left, ← map_mul]
    simp [io_one_one]

theorem leftInv_negIntegrand {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) {f₁ f₂ : GA D V → ℂ} (hf₁ : LeftInv (GQ V) f₁)
    (hf₂ : LeftInv (GQ V) f₂) : LeftInv ((GQ V).prod (GQ V))
      (dblIntegrand V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h₁, h₂⟩ ⟨g₁, g₂⟩
  have hE : (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) =
      ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂)) := by
    refine (tsum_congr fun q => ?_).trans ((ioEquiv h₁ h₂).tsum_eq
      (fun q : NegCosets V => φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))))
    show _ = φ ((((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1).out : GQ (dblSp V)) : GA D (dblSp V)) *
      io V (g₁, g₂))
    rw [apply_out_rmul hμ hφ, map_mul, mul_assoc]
  show (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) *
      conj (f₁ (γ₁ * g₁)) * f₂ (γ₂ * g₂) * (μ (detA V (γ₂ * g₂)) : ℂ)⁻¹ =
    (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))) *
      conj (f₁ g₁) * f₂ g₂ * (μ (detA V g₂) : ℂ)⁻¹
  rw [hE, hf₁ γ₁ h₁, hf₂ γ₂ h₂, map_mul, map_mul, apply_detA hμ h₂, one_mul]

theorem integral_neg_eq_zero : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hc
  haveI := hm
  show ∫ x, dblIntegrandQ V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x
    ∂(autMeasure V m).prod (autMeasure V m) = 0
  set E : GA D (dblSp V) → ℂ := fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)
    with hEdef
  by_cases hI : Integrable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m))
  swap
  · exact integral_undef hI
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_negIntegrand hμ hφ h₁.1 h₂.1
  have hconv : DblConv V μ m E f₁ f₂ := ⟨hli, hI⟩
  have h𝓕 : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V)
  obtain ⟨hint, heq⟩ := hconv.dblInt_eq h𝓕
  refine (heq : dblInt V μ m E f₁ f₂ = _).trans ?_
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [← Measure.prod_restrict, integral_prod_symm _ hint]
  have hφc : Continuous φ := hφ.2.1
  have hcont : ∀ q : SiegelCosets V, Continuous
      (dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂) := fun q =>
    continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous h₂.continuous
  set G : SiegelCosets V → GA D V × GA D V → ENNReal := fun q x =>
    ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ with hGdef
  have hGm : ∀ q, Measurable (G q) := fun q => (hcont q).measurable.enorm
  have hfin := (GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 h𝓕
  rw [← Measure.prod_restrict, ← lintegral_tsum fun q => (hGm q).aemeasurable,
    lintegral_prod_symm _ (Measurable.ennreal_tsum hGm).aemeasurable] at hfin
  have hae := ae_lt_top (Measurable.ennreal_tsum hGm).lintegral_prod_left' hfin
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with g₂ hg₂
  set Φ : NegCosets V → GA D V → ℂ := fun y h =>
    dblIntegrand V μ (fun x => φ (((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ (h, g₂) with hΦdef
  have hpt : ∀ g₁, dblIntegrand V μ E f₁ f₂ (g₁, g₂) = ∑' y, Φ y g₁ := fun g₁ => by
    simp only [hΦdef, dblIntegrand, hEdef]
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right]
  have hΦm : ∀ y, Measurable (Φ y) := fun y =>
    ((hcont y.1).comp (continuous_id.prodMk continuous_const)).measurable
  have hsum : ∑' y, ∫⁻ h, ‖Φ y h‖ₑ ∂(m.restrict 𝓕) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hg₂.ne ?_
    have hl := lintegral_tsum (μ := m.restrict 𝓕) (f := fun q h => G q (h, g₂))
      fun q => ((hGm q).comp measurable_prodMk_right).aemeasurable
    rw [hl]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun q => ∫⁻ h, G q (h, g₂) ∂(m.restrict 𝓕))
  rw [integral_congr_ae (.of_forall hpt), integral_tsum (fun y => (hΦm y).aestronglyMeasurable) hsum]
  refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero (GA D V) m (GQ V) (NegCosets V) 𝓕 h𝓕 Φ hΦm ?_ hsum ?_
  · intro γ y h
    have e : io V ((γ : GA D V)⁻¹, 1) * io V (γ * h, g₂) = io V (h, g₂) := by
      rw [← map_mul]; simp
    simp only [hΦdef, dblIntegrand]
    rw [h₁.1 _ γ.2, smul_val, apply_out_rmul hμ hφ, mul_assoc _ _ (io V _)]
    erw [e]
  · intro y 𝓖 h𝓖 hi
    exact GlobalTheory.T.doublingNegligibleOrbit_unfoldedIntegral_eq_zero D V a μ hμ s φ hφ _ (y.1.out).2 y.2 f₁ f₂ h₁.continuous h₂.continuous h₁.1 hc g₂ _
      (mem_map_stabilizer_iff y) m hm 𝓖 h𝓖 hi

end GlobalTheory.Core.Rk.NegOrbit
