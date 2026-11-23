import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) :
    (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  show u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  simp

theorem mul_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g h : UA σ X.J} (hg : g ∈ UAt σ X ev) (hh : h ∈ UAt σ X ev) : g * h ∈ UAt σ X ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    show mat g * mat h - 1 = _
    noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem inv_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g : UA σ X.J} (hg : g ∈ UAt σ X ev) : g⁻¹ ∈ UAt σ X ev := by
  intro u hu
  have h1 : mat g⁻¹ * mat g = 1 := by
    show ((g⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
    rw [inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locGrp {σ : E →ₐ[F] E} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    Subgroup (UA σ X.J × UA σ W.J) where
  carrier := {x | x.1 ∈ UAt σ X (evFin F v) ∧ x.2 ∈ UAt σ W (evFin F v)}
  one_mem' := ⟨one_mem_uAt X _, one_mem_uAt W _⟩
  mul_mem' ha hb := ⟨mul_mem_uAt X _ ha.1 hb.1, mul_mem_uAt W _ ha.2 hb.2⟩
  inv_mem' ha := ⟨inv_mem_uAt X _ ha.1, inv_mem_uAt W _ ha.2⟩

def tensL {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ R
  map_add' φ ψ := funext fun x => by simp [tens, add_mul]
  map_smul' c φ := funext fun x => by simp [tens, mul_assoc]

def locOp {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Module.End ℂ ((κ → Fv F v) → ℂ) :=
  (R 0)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun (t : κ → Fv F v) i => GlobalTheory.LatVac.liftV v (t i)) ∘ₗ T ∘ₗ tensL v R)

theorem tens_liftV {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (φ : (κ → Fv F v) → ℂ)
    (hR : Rest (evFin F v) φ R) (t : κ → Fv F v) :
    tens (evFin F v) φ R (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ t * R 0 := by
  have h1 := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i)) fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (t i) u hu
  rw [zero_add] at h1
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1]

theorem locOp_eq {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) {φ φ₁ : (κ → Fv F v) → ℂ}
    (hR : Rest (evFin F v) φ R) (hR₁ : Rest (evFin F v) φ₁ R) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    (h : Acts (evFin F v) T φ φ₁) : locOp v R T φ = φ₁ := by
  funext t
  have := h R hR
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply]
  change (R 0)⁻¹ • T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ₁ t
  rw [this, tens_liftV v φ₁ hR₁ t, smul_eq_mul]
  field_simp

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_fst (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl

open scoped Classical in

theorem continuous_locOp {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil B.ψ χX χW om) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (R : (Fin n × Fin d → AF F) → ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (lam : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) :
    Continuous fun x : UA σ X.J × UA σ W.J => lam (locOp v R (om x) φ) := by
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun (t : Fin n × Fin d → Fv F v) i => GlobalTheory.LatVac.liftV v (t i))
  have hl : lam ∘ₗ L ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨lam (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : L (GlobalTheory.WeilM.pureA F f g) = f 0 • (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) := by
      funext t
      simp only [L, LinearMap.funLeft_apply, GlobalTheory.WeilM.pureA, liftV_fst, map_zero, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [LinearMap.comp_apply, e, map_smul, smul_eq_mul, _root_.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hc := hW.2.2 (lam ∘ₗ L) hl _ hΦ
  have h2 : Continuous fun x : UA σ X.J × UA σ W.J => (R 0)⁻¹ * (lam ∘ₗ L) (om x (tens (evFin F v) φ R)) :=
    continuous_const.mul hc
  refine h2.congr fun x => ?_
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  rfl

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem weil_smooth_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v hActs φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  let H := locGrp (σ := σ) X W v
  let V := GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)
  have key : ∀ x ∈ H, ∀ ψ ∈ V, locOp v R (om x) ψ ∈ V ∧ Acts (evFin F v) (om x) ψ (locOp v R (om x) ψ) := by
    intro x hx ψ hψ
    obtain ⟨ψ₁, hψ₁, hA⟩ := hActs x hx.1 hx.2 ψ hψ
    rw [locOp_eq v hR0 (hR ψ hψ) (hR ψ₁ hψ₁) hA]
    exact ⟨hψ₁, hA⟩
  classical
  let S : UA σ X.J × UA σ W.J → Module.End ℂ V := fun x =>
    if hx : x ∈ H then (locOp v R (om x)).restrict (fun ψ hψ => (key x hx ψ hψ).1) else LinearMap.id
  have hS : ∀ x (hx : x ∈ H) (ψ : V), ((S x ψ : V) : (Fin n × Fin d → Fv F v) → ℂ) = locOp v R (om x) ψ := by
    intro x hx ψ
    simp only [S, dif_pos hx]
    rfl
  have hmul : ∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y := by
    intro x hx y hy
    ext ψ : 1
    apply Subtype.ext
    rw [hS _ (H.mul_mem hx hy), Module.End.mul_apply, hS _ hx, hS _ hy]
    have h1 := key y hy ψ ψ.2
    have h2 := key x hx _ h1.1
    refine locOp_eq v hR0 (hR ψ ψ.2) (hR _ h2.1) fun r hr => ?_
    have hr' : Rest (evFin F v) (locOp v R (om y) ψ) r := ⟨hr.1, by
      rw [← h1.2 r hr]
      exact (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil).pres y _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1.2 r hr, h2.2 r hr']
  have hone : S 1 = 1 := by
    ext ψ : 1
    apply Subtype.ext
    rw [hS 1 H.one_mem]
    exact locOp_eq v hR0 (hR ψ ψ.2) (hR ψ ψ.2) fun r _ => by rw [map_one]; rfl
  have hcont : ∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set (UA σ X.J × UA σ W.J)) := by
    intro l w
    obtain ⟨lam, hlam⟩ := LinearMap.exists_extend l
    refine (continuous_locOp hP.weil v R w.1 (hR w.1 w.2).2 lam).continuousOn.congr fun x hx => ?_
    have : S x w = ⟨locOp v R (om x) w, (key x hx w w.2).1⟩ := Subtype.ext (hS x hx w)
    rw [this, ← hlam]
    rfl
  have hbasis : ∀ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∃ K : Subgroup (UA σ X.J × UA σ W.J), K ≤ H ∧
      IsCompact (K : Set (UA σ X.J × UA σ W.J)) ∧
      (∃ O : Set (UA σ X.J × UA σ W.J), IsOpen O ∧ (1 : UA σ X.J × UA σ W.J) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧
      (K : Set (UA σ X.J × UA σ W.J)) ⊆ U := by
    intro U hU
    rw [show (1 : UA σ X.J × UA σ W.J) = (1, 1) from rfl, nhds_prod_eq] at hU
    obtain ⟨U1, hU1, U2, hU2, hsub⟩ := Filter.mem_prod_iff.1 hU
    obtain ⟨K1, hK1H, hK1c, ⟨O1, hO1, h1O1, hO1K⟩, hK1U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ X v U1 hU1
    obtain ⟨K2, hK2H, hK2c, ⟨O2, hO2, h1O2, hO2K⟩, hK2U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ W v U2 hU2
    refine ⟨K1.prod K2, fun x hx => ⟨hK1H _ hx.1, hK2H _ hx.2⟩, ?_,
      ⟨O1 ×ˢ O2, hO1.prod hO2, ⟨h1O1, h1O2⟩, fun x hx hxH => ⟨hO1K _ hx.1 hxH.1, hO2K _ hx.2 hxH.2⟩⟩,
      fun x hx => hsub ⟨hK1U hx.1, hK2U hx.2⟩⟩
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  obtain ⟨U, hU, hfix⟩ := GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded H S hmul hone hcont hbasis ⟨φ, hφ⟩
  refine ⟨U, hU, fun x hxU hx1 hx2 => ?_⟩
  have hx : x ∈ H := ⟨hx1, hx2⟩
  have e := congrArg Subtype.val (hfix x hxU hx)
  rw [hS x hx] at e
  have := (key x hx φ hφ).2
  rwa [e] at this

end GlobalTheory.SmoothAtPlace
