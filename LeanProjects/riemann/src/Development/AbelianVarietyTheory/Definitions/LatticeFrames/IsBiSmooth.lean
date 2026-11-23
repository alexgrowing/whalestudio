import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RapidVal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def IsBiSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

structure IsBiTheta (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  smooth : IsBiSmooth C
  quasiL : ∀ γ u v, C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v
  quasiR : ∀ γ u v, C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v
  levL : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v
  levR : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u

def BiAct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'),
    IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C →
      (∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u) ∧
      (∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v) ∧
      (∀ p q u v, omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u) ∧
      Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
        omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2

def FockRed (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

def IsRealS (j : ℕ) (C : WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ) : Prop :=
  d.IsReal j C ∧ IsBiSmooth C

def ValS : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (d.st (j + 1)).V, ∀ a' ∈ GinfC (d.st (j + 1 + 1)).V,
    ∃ C, d.IsRealS j C ∧ ∀ ψ ∈ d.Ram j, ∀ y,
      d.hand j σ h P₁ P₂ (d.rd j ψ y) (a * d.t (j + 1)) (a' * d.t (j + 1 + 1)) = d.two j (d.rd j (d.S j ψ) y) C

def ValLastS : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) P₁ P₂, ∃ C, d.IsRealS j C ∧ ∀ ψ ∈ d.Ram j, ∀ y (F : d.top.st.CC d.c) (v : SmT d.top.M),
    (d.B j 0 h).per d.c.ψ (d.rd j ψ y) (rTrans (d.t j) (liftS (d.p j).ω (d.st (j + 1)).ν (d.st (j + 1)).fd
        (liftS (d.pT j h).ω d.top.ν d.top.fd (F.1 v) ((d.pT j h).pt P₂)) ((d.p j).pt P₁))) =
      ∫ h' in d.top.fd, F.1 v h' * d.two j (d.rd j (d.S j ψ) y) C ((d.oT (j + 1 + 1) h).emb (h', 1)) ∂d.top.ν

def TwoColS : Prop :=
  ∀ j, j + 2 ≤ D.R.m → ∀ C, d.IsRealS j C → ∀ y, ∃ a : (D.mem u).C.Y (j + 1 + 1) →₀ ℂ, ∀ ψ ∈ d.Ram j,
    d.two j (d.rd j ψ y) C = ∑ y' ∈ a.support, a y' • d.rd (j + 1 + 1) ((D.mem u).C.K (j + 1) ((D.mem u).C.K j ψ)) y'

end Dat

section Examples

variable {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D}

example {f : WO A S → ℂ} {g : WO S A' → ℂ} (hf : IsThetaFunO ψ A S f) (hg : IsThetaFunO ψ S A' g) :
    IsBiTheta ψ A S A' fun u v => f u * g v where
  cont := (hf.cont.comp continuous_fst).mul (hg.cont.comp continuous_snd)
  smooth := fun n L L' hL hL' h0 h0' u v => (hf.smooth n L hL h0 u).mul (hg.smooth n L' hL' h0' v)
  quasiL := fun γ u v => by rw [hf.quasi, mul_assoc]
  quasiR := fun γ u v => by rw [hg.quasi, mul_left_comm]
  levL := by
    obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U, hU, fun a ha h0 v => funext fun w => ?_⟩
    have e := congrFun (h a ha h0) w
    simp only [heisO] at e ⊢
    rw [← mul_assoc, e]
  levR := by
    obtain ⟨U, hU, h⟩ := hg.level
    refine ⟨U, hU, fun a ha h0 u => funext fun w => ?_⟩
    have e := congrFun (h a ha h0) w
    simp only [heisO] at e ⊢
    rw [mul_left_comm, e]

example {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (v : WO S A') : IsThetaFunO ψ A S fun u => C u v where
  quasi := fun γ u => h.quasiL γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levL
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 v⟩
  cont := h.cont.comp (continuous_id.prodMk continuous_const)
  smooth := fun n L hL h0 u => by
    have := h.smooth n L 0 hL continuous_const h0 (fun _ => Matrix.map_zero _ (map_zero (finPart D))) u v
    simpa using this

example {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (u : WO A S) : IsThetaFunO ψ S A' (C u) where
  quasi := fun γ v => h.quasiR γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levR
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 u⟩
  cont := h.cont.comp (continuous_const.prodMk continuous_id)
  smooth := fun n L hL h0 v => by
    have := h.smooth n 0 L continuous_const hL (fun _ => Matrix.map_zero _ (map_zero (finPart D))) h0 u v
    simpa using this

example {u : D.what₂.Word} (d : Dat D u) (C : WO A S → WO S A' → ℂ) :
    (IsBiSmooth C ↔ JointSmooth C) ∧ (d.ValS ↔ d.Val) ∧ (d.ValLastS ↔ d.ValLast) ∧ (FockRed D ↔ FockReduce D) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

end Examples

end GlobalTheory.SeeSaw

end
