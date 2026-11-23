import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingStepsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LastStepsX

variable {D : D7}

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (a : ℂ)
    (G : GA D T → ℂ) (f : WO S T → ℂ) : liftS om ν 𝓕 (a • G) f = a • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS, Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (a : ℂ) (f : GA D V → ℂ) : trc e (a • f) = a • trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem perF_smul {c : Comm D} (t : Tup c) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (a : ℂ) (f : GA D (c.V j) → ℂ) : t.perF j ρ h φ (a • f) = a * t.perF j ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e := GlobalTheory.HandHom.per_smul (c.B j ρ h) c.ψ 1 a (φ α) (trc (t.e j α) f)
  rw [one_smul, one_mul] at e
  exact e

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hf.1 γ hγ]
  · have e : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := by
      funext x
      simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact continuous_finset_sum _ fun g _ => continuous_const.mul (hf.2.comp (continuous_mul_right g))

theorem contAut_emb {S A B : HSp D} (o : OrthDec S A B) {f : GA D S → ℂ} (hf : IsContAut S f) :
    Continuous (fun h : GA D A => f (o.emb (h, 1))) ∧ ∀ γ ∈ GQ A, ∀ g, f (o.emb (γ * g, 1)) = f (o.emb (g, 1)) := by
  refine ⟨hf.2.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const)), fun γ hγ g => ?_⟩
  have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, hf.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integrableOn_contAut {V : HSp D} (hV : CoCpt V) (vol : Vol V) {f : GA D V → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : IntegrableOn f vol.𝓕 vol.μ :=
  (GlobalTheory.CocompactParam.continuous_integral_param D V hV vol Unit (fun g _ => f g) (hc.comp continuous_fst)
    (fun γ hγ g _ => hi γ hγ g)).1 ()

theorem io_ioT {c : Comm D} (t : Tup c) (ht : t.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (F : t.CT)
    (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank) (P₂ : PolF D c.T.rank (c.V (j + 1)).rank) (v : SmT c.MT) :
    (t.cI j * t.cI (j + 1)) • ((t.io j (t.ioT j h F)).1 (c.It j P₁ (c.ItT j h P₂ v))) =
      liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P₂)) (t.pt j P₁) := by
  rw [ht.ioT j h F P₂ v, liftS_smul, ht.io j (by omega) (t.ioT j h F) P₁ (c.ItT j h P₂ v), smul_smul, mul_comm]

theorem perT_comb {c : Comm D} (t : Tup c) (n : ℕ) (h : n = D.R.m) {Y : Type} (S : Finset Y) (k : ℂ) (a : Y → ℂ)
    (φ : Y → t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ)
    (hi : ∀ y' β, IntegrableOn (fun h' => trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) c.volT.𝓕 c.volT.μ) :
    t.perT n h (fun β => k • ∑ y' ∈ S, a y' • φ y' β) f = k * ∑ y' ∈ S, a y' * t.perT n h (φ y') f := by
  have e1 : ∀ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1)) ∂c.volT.μ
      = ∑ y' ∈ S, k * a y' * ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1)) ∂c.volT.μ := by
    intro β
    have e2 : (fun h' => trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1))) =
        fun h' => ∑ y' ∈ S, (k * a y') * (trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) := by
      funext h'
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e2, integral_finset_sum _ (fun y' _ => (hi y' β).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [Tup.perT, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun β _ => by ring

end GlobalTheory.SeeSaw.LastStepsX

set_option maxHeartbeats 4000000 in
open GlobalTheory.SeeSaw.LastStepsX in

theorem GlobalTheory.SeeSaw.lastX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  intro hHC D c 𝒯 t hRV hc ht hVL hTX hPX hRD
  intro j h I _ s α ψ F hψ hF y v
  obtain ⟨χ, hχ⟩ := hRD j (by omega)
  obtain ⟨χ₂, hχ₂⟩ := hRD (j + 1 + 1) (by omega)
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j 0 h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i β => (t (s i)).rd j β (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).ioT j h (F i))) ht
    (fun i β => (hχ (s i) (ψ i) (hψ i) β y).1) c.T c.T c.parT c.MT (c.ItT j h) (hc.spanT j h) ?_ v
  intro P₁ P₂ w
  obtain ⟨C, hCr, hC⟩ := hVL j h P₁ P₂
  obtain ⟨a, ha⟩ := hTX j (by omega) C hCr y
  choose b hb using fun y' => hPX (j + 1 + 1) h y' w
  have hterm : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j 0 h (fun β => (t (s i)).rd j β (ψ i) y)
      (((t (s i)).io j ((t (s i)).ioT j h (F i))).1 (c.It j P₁ (c.ItT j h P₂ w))) =
      ∑ y' ∈ a.support, a y' * b y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) *
        (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i)) := by
    intro i
    have hSψ : (t (s i)).S j (ψ i) ∈ (t (s i)).Ram j := (ht (s i)).stabS j (by omega) _ (hψ i)
    have hψ₁ := (ht (s i)).stabK j (by omega) _ hSψ
    have hψ₂ := (ht (s i)).stabK (j + 1) (by omega) _ hψ₁
    rw [mul_assoc, ← perF_smul, io_ioT (t (s i)) (ht (s i)) j h (F i) P₁ P₂ w, hC (s i) (ψ i) (hψ i) y (F i) w]
    have e2 : (t (s i)).two j (fun β => (t (s i)).rd j β ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ a.support, a y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext fun β => ha (s i) _ hSψ β
    have hE : RapidDec c.T ((F i).1 w) := by
      obtain ⟨J, χ', hle⟩ := (ht (s i)).CT
      exact hRV c.θ hc.inf c.T c.parT c.MT J χ' _ (hle (F i).2) w
    have e3 := perT_comb (t (s i)) (j + 1 + 1) h a.support ((t (s i)).cK j * (t (s i)).cK (j + 1)) a
      (fun y' β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w)
      (fun y' β => by
        have ht' := contAut_trc ((t (s i)).eT (j + 1 + 1) h β) ⟨hE.1, hE.2.1⟩
        obtain ⟨hcont, hinv⟩ := contAut_emb (c.oT (j + 1 + 1) h) (hχ₂ (s i) _ hψ₂ β y').1
        exact integrableOn_contAut hc.cpt c.volT (ht'.2.mul hcont) (fun γ hγ g => by rw [ht'.1 γ hγ g, hinv γ hγ g]))
    beta_reduce at e3
    have hb' : ∀ y', (t (s i)).perT (j + 1 + 1) h
        (fun β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w) =
        (t (s i)).cP * b y' * (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) :=
      fun y' => hb y' (s i) _ hψ₂ (F i)
    rw [e2, e3]
    simp only [hb', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hF, mul_zero]

end
