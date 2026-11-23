import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized

noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_add_le (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (P + Q) x ≤ X.pnorm la P x + X.pnorm la Q x := by
  simp only [Data.pnorm, Pi.add_apply]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pnorm_fac_nonneg X la x)

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem pnorm_zero (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : X.pnorm la 0 x = 0 := by
  simp [Data.pnorm]

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la := Submodule.subset_span h

def dmet (n f r : ℕ) : ℝ := Real.exp ((n : ℝ) * f * r * (-(1 / 2) * Real.log (2 * Real.pi)) / 2)

theorem supN_nonneg (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : 0 ≤ supN X la P := ENNReal.toReal_nonneg

variable (V : HSp D)

def adel {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) :
    FDSec X →ₗ[ℂ] (GA D V → ℂ) where
  toFun P := fun g => mu g * P (dict g).1 (dict g).2
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' a P := by funext g; simp [mul_left_comm]

def onQ : (GA D V → ℂ) →ₗ[ℂ] (AutQ V → ℂ) where
  toFun φ := fun q => φ q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SS {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Submodule ℂ (Lp ℂ 2 (muQ1 V)) :=
  Submodule.span ℂ {F | ∃ P : FDSec X, IsHolCusp X la P ∧
    ∃ h : MemLp (onQ V (adel V dict mu P)) 2 (muQ1 V), F = h.toLp _}

variable {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)

def jFn {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : C →ₛₗ[σ] (AutQ V → ℂ) :=
  (onQ V ∘ₗ adel V dict mu).comp rd

def RdHolCusp {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X) : Prop :=
  ∀ f, IsHolCusp X la (rd f)

def RdInj {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) : Prop := Function.Injective rd

def JMemL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Prop :=
  ∀ f, MemLp (jFn V σ rd dict mu f) 2 (muQ1 V)

def uniformisationL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : C →ₛₗ[σ] Lp ℂ 2 (muQ1 V) where
  toFun f := (h f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    congr 1
    exact map_add _ f g
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    congr 1
    exact map_smulₛₗ _ a f

theorem jL2_mem_span {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)
    (h1 : RdHolCusp σ la rd) (f : C) : uniformisationL2 V σ rd dict mu h f ∈ SS V la dict mu := Submodule.subset_span ⟨rd f, h1 f, h f, rfl⟩

def jSS {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)
    (h1 : RdHolCusp σ la rd) : C →ₛₗ[σ] SS V la dict mu :=
  (uniformisationL2 V σ rd dict mu h).codRestrict _ (jL2_mem_span V σ la rd dict mu h h1)

def l2NormAlt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : ℝ :=
  ‖uniformisationL2 V σ rd dict mu h f‖

theorem l2Norm_nonneg_bis {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : 0 ≤ l2NormAlt V σ rd dict mu h f := norm_nonneg _

theorem l2Norm_smul_alt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (a : K) (f : C) :
    l2NormAlt V σ rd dict mu h (a • f) = ‖σ a‖ * l2NormAlt V σ rd dict mu h f := by
  simp only [l2NormAlt, map_smulₛₗ, norm_smul]

theorem L2Norm_add_le {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f g : C) :
    l2NormAlt V σ rd dict mu h (f + g) ≤ l2NormAlt V σ rd dict mu h f + l2NormAlt V σ rd dict mu h g := by
  simp only [l2NormAlt, map_add]
  exact norm_add_le _ _

def JInj {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => uniformisationL2 V σ rd dict mu h (b i))

def L2Definite {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ f, l2NormAlt V σ rd dict mu h f = 0 → f = 0

def FinVol : Prop := muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤

def archM (th' : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (infHom V h).1.map th'

def archMat {X : Comp → Data E r} (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (x0 : ∀ c, Frame (X c).Ψ r) (h : GA D V) (c : Comp) : Frame (X c).Ψ r :=
  fun τ => ((mat (x0 c) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) h) * mat (x0 c) τ :
    Matrix (Fin r) (Fin r) ℂ)

def DictIsUnif {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r) : Prop :=
  (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∃ x0 : ∀ c, Frame (X c).Ψ r, (∀ c, x0 c ∈ (X c).dom ∧ ∃ g, dict g = ⟨c, x0 c⟩) ∧
      ∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
        dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th hr x0 h (dict g).1))⟩) ∧
    (∀ g, (dict g).2 ∈ (X (dict g).1).dom) ∧
    (∀ c, ∀ x ∈ (X c).dom, ∃ g, ∃ γ ∈ (X c).Γ, ∃ b ∈ Bor (X c).Ψ r, dict g = ⟨c, rmul (lact γ x) b⟩) ∧
    ∀ g g', (∃ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k

def repOf {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (c : Comp) : GA D V :=
  Classical.epsilon fun g => (dict g).1 = c

def detGf {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (c : Comp) :
    (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  Matrix.GeneralLinearGroup.det (finHom V (repOf V dict c))

def MuUnit {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) : Prop :=
  (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧
    ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1

theorem pnorm_eq_of_unit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (h : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  simp [Data.pnorm, norm_div, h]

theorem L2Norm_le_sup_norm {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)
    (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu) (f : C)
    (hfin : supE X la (rd f) ≠ ⊤) : l2NormAlt V σ rd dict mu h f ≤ supN X la (rd f) := by
  haveI : IsProbabilityMeasure (muQ1 V) := by
    unfold muQ1
    split_ifs with hh
    · constructor
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hh.1 hh.2]
    · infer_instance
  have hC : 0 ≤ supN X la (rd f) := supN_nonneg X la (rd f)
  have hb : ∀ᵐ q ∂(muQ1 V), ‖(uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q‖ ≤ supN X la (rd f) := by
    filter_upwards [(h f).coeFn_toLp] with q hq
    have hq' : (uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q = jFn V σ rd dict mu f q := hq
    rw [hq']
    show ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖ ≤ _
    rw [norm_mul, hm.2.1, one_mul,
      ← pnorm_eq_of_unit (X (dict q.out).1) (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 (hm.2.2.2 q.out)]
    have h1 : ENNReal.ofReal ((X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2)
        ≤ supE X la (rd f) :=
      le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (rd f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd q.out⟩⟩
    have h0 : 0 ≤ (X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal h0] at h2
  have := Lp.norm_le_of_ae_bound hC hb
  simpa [l2NormAlt, measureUnivNNReal] using this

def DictTie {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (chiK : Kf →* ℂˣ) : Prop :=
  ∀ P : FDSec X, IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧
    ∀ k : Kf, ∀ g, adel V dict mu P (g * k) = ((chiK k : ℂˣ) : ℂ) * adel V dict mu P g

def UnifOnto {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  Submodule.span ℂ (Set.range (uniformisationL2 V σ rd dict mu h)) = SS V la dict mu

def EquivariantFiniteGroup {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) :
    Prop :=
  ∀ g f x, adel V dict mu (rd (ρ g f)) x = σ ((chi g : Kˣ) : K) * adel V dict mu (rd f) (x * ℓ g)

def HeckeTie {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) {T : Type} (hL : T → C →ₗ[K] C) (R : T → Finset (GA D V)) : Prop :=
  ∀ t f x, adel V dict mu (rd (hL t f)) x = ∑ γ ∈ R t, adel V dict mu (rd f) (x * γ)

end Formalism.L2.Pj
