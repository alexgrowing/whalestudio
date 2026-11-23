import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

section LA

variable {ι Q : Type} [AddCommGroup Q] [Module ℂ Q]

def IsStab (ρ : ι → Module.End ℂ Q) (N : Submodule ℂ Q) : Prop := ∀ i, ∀ x ∈ N, ρ i x ∈ N

def HoweCond (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ Q), StrictMono N → (∀ k, IsStab ρ (N k) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ Q, IsStab ρ N → C ≤ N → N ≠ ⊤ → IsStab ρ N' → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

def rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Submodule ℂ Q :=
  sSup {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}

theorem isStab_rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : IsStab ρ (rad ρ C) := by
  intro i
  have h : rad ρ C ≤ (rad ρ C).comap (ρ i) := by
    refine sSup_le fun N hN => ?_
    intro x hx
    exact le_sSup hN (hN.1 i x hx)
  exact fun x hx => h hx

def radAct (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) : Module.End ℂ (Q ⧸ rad ρ C) :=
  (rad ρ C).mapQ (rad ρ C) (ρ i) fun x hx => isStab_rad ρ C i x hx

theorem radAct_mk (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) (x : Q) :
    radAct ρ C i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ i x) := rfl

end LA

section Fock

variable {D : D7}

def actT (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) + ((eS τ : ℂ) * Y.trace) • 1

def actS (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin M.rank) (Fin M.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) -
    ((eT τ : ℂ) * Z.trace) • 1

def coinv (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) : Submodule ℂ (PolF D X.rank M.rank) :=
  Submodule.span ℂ {P | ∃ τ, ∃ Z ∈ lieAt M τ, ∃ P₀, P = actS ε A B eT τ Z P₀}

abbrev LieIx (X : HSp D) : Type := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}

end Fock

section LALemmas

theorem isStab_sup {ι Q : Type} [AddCommGroup Q] [Module ℂ Q] {ρ : ι → Module.End ℂ Q} {N N' : Submodule ℂ Q}
    (h : IsStab ρ N) (h' : IsStab ρ N') : IsStab ρ (N ⊔ N') := by
  intro i x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (h i y hy) (h' i z hz)

theorem rad_ne_top : ∀ (ι Q : Type) [AddCommGroup Q] [Module ℂ Q] (ρ : ι → Module.End ℂ Q) (C N₀ : Submodule ℂ Q),
  GlobalTheory.RealQuot.HoweCond ρ C → GlobalTheory.RealQuot.IsStab ρ N₀ → C ≤ N₀ → N₀ ≠ ⊤ → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ := by
  intro ι Q _ _ ρ C N₀ hH hs hC hne
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH
  let S : Set (Submodule ℂ Q) := {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}
  have wf : WellFounded (fun x y : S => y.1 < x.1) := by
    refine ⟨fun x => ?_⟩
    by_contra hx
    obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.1 hx
    have mono : StrictMono fun n => (f n).1 := strictMono_nat_of_lt_succ hf
    have := hL (L + 1) (fun k => (f k).1) (mono.comp Fin.val_strictMono) fun k => ⟨(f k).2.1, (f k).2.2.1⟩
    omega
  obtain ⟨M, -, hM⟩ := wf.has_min Set.univ ⟨⟨N₀, hs, hC, hne⟩, trivial⟩
  have hmax : ∀ N ∈ S, N ≤ M.1 := by
    intro N hN
    have hs' : M.1 ⊔ N ∈ S := ⟨isStab_sup M.2.1 hN.1, le_sup_of_le_left M.2.2.1,
      hsum _ _ M.2.1 M.2.2.1 M.2.2.2 hN.1 hN.2.1 hN.2.2⟩
    by_contra h
    exact hM ⟨_, hs'⟩ trivial (lt_of_le_of_ne le_sup_left fun e => h (e ▸ le_sup_right))
  have e : rad ρ C = M.1 := le_antisymm (sSup_le hmax) (le_sSup M.2)
  rw [e]
  exact M.2.2.2

theorem rad_le_ker : ∀ (ι Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (β : Q →ₗ[ℂ] Pi),
  (∀ i, β ∘ₗ ρ i = σ i ∘ₗ β) → C ≤ LinearMap.ker β → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker β := by
  intro ι Q Pi _ _ _ _ ρ C σ β hi hk hrad hss
  by_contra hne
  have hKs : IsStab ρ (LinearMap.ker β) := fun i x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  have hK : LinearMap.ker β ≠ ⊤ := fun h => hne (h ▸ le_top)
  have hTs : IsStab σ ((rad ρ C).map β) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, isStab_rad ρ C i x hx, by rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]⟩
  obtain ⟨N', hN's, hc⟩ := hss _ hTs
  have hUs : IsStab ρ (N'.comap β) := fun i x hx => by
    show β (ρ i x) ∈ N'
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]
    exact hN's i _ hx
  have hCU : C ≤ N'.comap β := fun x hx => by
    show β x ∈ N'
    rw [LinearMap.mem_ker.1 (hk hx)]
    exact N'.zero_mem
  have hsup : rad ρ C ⊔ N'.comap β = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : β x ∈ (rad ρ C).map β ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht, n, hn, htn⟩ := Submodule.mem_sup.1 h1
    obtain ⟨r, hr, rfl⟩ := ht
    have h2 : x - r ∈ N'.comap β := by
      show β (x - r) ∈ N'
      rw [map_sub, ← htn, add_sub_cancel_left]
      exact hn
    have h3 := Submodule.add_mem_sup hr h2
    rwa [add_sub_cancel] at h3
  by_cases hU : N'.comap β = ⊤
  · apply hne
    intro x hx
    have h1 : β x ∈ (rad ρ C).map β := ⟨x, hx, rfl⟩
    have h2 : β x ∈ N' := by
      have : x ∈ N'.comap β := hU ▸ Submodule.mem_top
      exact this
    have h3 : β x ∈ (rad ρ C).map β ⊓ N' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h3
    exact h3
  · exact hrad (eq_top_iff.2 (hsup ▸ sup_le le_rfl (le_sSup ⟨hUs, hCU, hU⟩)))

end LALemmas

theorem hasInfExp_div : ∀ (D : D7) (α β : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D α τ a → HasInfExp D β τ b →
  HasInfExp D (β / α) τ (b - a) := by
  intro D α β τ a b hA hB
  obtain ⟨m, hm, ex, hα⟩ := hA
  obtain ⟨n, hn, -, hβ⟩ := hB
  refine ⟨n - m, by push_cast; rw [hm, hn]; ring, ex, fun θ hθ x h1 h2 => ?_⟩
  have eα := hα θ hθ x h1 h2
  have eβ := hβ θ hθ x h1 h2
  set w : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hw
  have hdiv : (((β / α) x : Circle) : ℂ) = ((β x : Circle) : ℂ) / ((α x : Circle) : ℂ) := by
    rw [MonoidHom.div_apply, Circle.coe_div]
  rw [hdiv, eα, eβ]
  rcases eq_or_ne w 0 with h0 | h0
  · have hm0 : m = 0 := by
      by_contra hm0
      have := eα
      rw [h0, _root_.zero_zpow _ hm0] at this
      exact Circle.coe_ne_zero _ this
    have hn0 : n = 0 := by
      by_contra hn0
      have := eβ
      rw [h0, _root_.zero_zpow _ hn0] at this
      exact Circle.coe_ne_zero _ this
    subst hm0 hn0
    simp
  · rw [zpow_sub₀ h0]

end GlobalTheory.RealQuot

end
