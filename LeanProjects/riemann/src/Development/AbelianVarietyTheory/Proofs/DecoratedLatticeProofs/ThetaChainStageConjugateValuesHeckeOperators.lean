import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjVal

variable {D : D7}

def Good (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g

theorem Good.add {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f f' : GA D V → ℂ}
    (h : Good V J χ f) (h' : Good V J χ f') : Good V J χ (f + f') := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  obtain ⟨c', ⟨C', hC'⟩, l', r'⟩ := h'
  refine ⟨c.add c', ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩,
    fun γ hγ g => by simp [l γ hγ g, l' γ hγ g], fun k hk g => by simp [r k hk g, r' k hk g, mul_add]⟩

theorem Good.smul {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f : GA D V → ℂ} (a : ℂ)
    (h : Good V J χ f) : Good V J χ (a • f) := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  refine ⟨continuous_const.mul c, ⟨‖a‖ * C, fun g => ?_⟩,
    fun γ hγ g => by simp [l γ hγ g], fun k hk g => by simp [r k hk g, mul_left_comm]⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)

theorem good_val (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    (u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : ⨂[ℂ] τ, M.sm τ) :
    Good V J χ (u v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT θ M J χ u).1 hu)
  have hu' : u = PiTensorProduct.lift (PiTensorProduct.lift.symm u) := (LinearEquiv.apply_symm_apply _ _).symm
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul]
    refine Good.smul a ?_
    rw [hu', PiTensorProduct.lift.tprod]
    exact ⟨(hT.aut x).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut x) (hT.cusp x), (hT.aut x).left,
      hT.lev x⟩
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

theorem conj_eq_one_iff' (z : ℂ) : conj z = 1 ↔ z = 1 := by
  constructor
  · intro h; simpa using congrArg conj h
  · intro h; simp [h]

theorem conj_values_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s =>
    (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧
      (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧
      ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧
    (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔
      Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧
    ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ),
      heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => good_val hP hc.inf (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v, fun P d R => ?_, fun R f => ?_⟩
  · simp only [Hecke₂, conj_eq_one_iff']
  · funext g
    simp [heckeLin, map_sum]

end GlobalTheory.ConjVal

end
