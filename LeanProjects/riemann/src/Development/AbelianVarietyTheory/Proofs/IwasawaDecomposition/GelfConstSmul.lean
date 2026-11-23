import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7}

def word (θ : InfF D) (V : HSp D) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    GA D V → ℂ := l.foldr (fun p f => Rder θ V p.1 p.2 f) φ

def IsMod (θ : InfF D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ ∃ (N : ℕ) (C : ℝ), ∀ g, ‖word θ V l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

private theorem word_mem_smFun {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : word θ V l φ ∈ SmFun θ V := by
  induction l with
  | nil => exact hφ
  | cons p l ih =>
    exact Rder_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hl p (by simp))

theorem word_add {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) :
    word θ V l (φ + ψ) = word θ V l φ + word θ V l ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    show Rder θ V p.1 p.2 (word θ V l (φ + ψ)) =
      Rder θ V p.1 p.2 (word θ V l φ) + Rder θ V p.1 p.2 (word θ V l ψ)
    rw [ih hl', Rder_add (word_mem_smFun hl' hφ) (word_mem_smFun hl' hψ) (hl p (by simp))]

theorem word_smul {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (c : ℂ) (φ : GA D V → ℂ) : word θ V l (c • φ) = c • word θ V l φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show Rder θ V p.1 p.2 (word θ V l (c • φ)) = c • Rder θ V p.1 p.2 (word θ V l φ)
    rw [ih fun q hq => hl q (List.mem_cons_of_mem _ hq), Rder_smul]

theorem word_Rder {θ : InfF D} {V : HSp D} (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    word θ V l (Rder θ V τ X φ) = word θ V (l ++ [(τ, X)]) φ := by
  unfold word
  rw [List.foldr_append]
  rfl

def Decay (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ IsRapidDecay θ V (word θ V l φ)}
  add_mem' := by
    rintro φ ψ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨add_mem a1 b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], fun l hl => ?_⟩
    rw [word_add hl a1 b1]
    refine ⟨(a3 l hl).1.add (b3 l hl).1, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    obtain ⟨C', hC'⟩ := (b3 l hl).2 N
    refine ⟨C + C', fun g => le_trans ?_ (add_le_add (hC g) (hC' g))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  zero_mem' := by
    refine ⟨zero_mem _, fun _ _ _ => rfl, fun l hl => ?_⟩
    have := word_smul (θ := θ) hl 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact ⟨continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  smul_mem' := by
    rintro c φ ⟨a1, a2, a3⟩
    refine ⟨Submodule.smul_mem _ c a1, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], fun l hl => ?_⟩
    rw [word_smul hl]
    refine ⟨(a3 l hl).1.const_smul c, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

theorem Rder_left {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    Rder θ V τ X φ (γ * g) = Rder θ V τ X φ g := by
  show deriv (fun t : ℝ => φ (γ * g * oneP θ V τ X t)) 0 = deriv (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simp only [mul_assoc, h]

theorem append_mem_lie {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    ∀ p ∈ l ++ [(τ, X)], p.2 ∈ lieAt V p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hl p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact hX

theorem Rder_mem_Decay {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : φ ∈ Decay θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ Decay θ V := by
  obtain ⟨h1, h2, h3⟩ := h
  refine (show _ ∧ _ ∧ _ from ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩)
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

theorem IsMod.rder {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : IsMod θ V φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : IsMod θ V (Rder θ V τ X φ) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold IsMod
  refine ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

private theorem word_const_eq_const_norm_le {θ : InfF D} {V : HSp D} (c : ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    ∃ d : ℂ, word θ V l (fun _ => c) = (fun _ => d) ∧ ‖d‖ ≤ ‖c‖ := by
  induction l with
  | nil => exact ⟨c, rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨d, hd, -⟩ := ih
    refine ⟨0, ?_, by simp⟩
    show Rder θ V p.1 p.2 (word θ V l fun _ => c) = _
    rw [hd]
    funext g
    simp [Rder]

theorem isMod_const (θ : InfF D) (V : HSp D) (c : ℂ) : IsMod θ V fun _ => c := by
  unfold IsMod
  refine ⟨?_, fun _ _ _ => rfl, fun l _ => ?_⟩
  · intro k τs Xs _ g
    exact contDiff_const
  · obtain ⟨d, hd, hdc⟩ := word_const_eq_const_norm_le (θ := θ) (V := V) c l
    rw [hd]
    exact ⟨continuous_const, 0, ‖c‖, fun _ => by rw [pow_zero, mul_one]; exact hdc⟩

structure IsKerSys (θ : InfF D) (V W : HSp D) {M : Type} [AddCommGroup M] [Module ℂ M]
    (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) : Prop where
  cont : ∀ f, Continuous fun p : GA D V × GA D W => κ f p.1 p.2
  left : ∀ f, ∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, κ f (γ * g) (δ * h) = κ f g h
  level : ∀ f, ∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧
    IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, κ f (g * k) (h * k') = κ f g h
  growth : ∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ g h, ‖κ f g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N
  derV : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f (g * oneP θ V τ X t) h) (κ f' g h) 0
  derW : ∀ τ, ∀ X ∈ lieAt W τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0
  cap : ∀ τ, ∃ a b : ℕ → Module.End ℂ M, (∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h) ∧
    (∀ k f g, gelf θ W τ k (κ f g) = κ (b k f) g) ∧ Algebra.adjoin ℂ (Set.range a) = Algebra.adjoin ℂ (Set.range b)

def swapKer {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) :
    M →ₗ[ℂ] (GA D W → GA D V → ℂ) where
  toFun f h g := κ f g h
  map_add' f f' := by rw [map_add]; rfl
  map_smul' c f := by rw [map_smul]; rfl

theorem IsKerSys.swap {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (h : IsKerSys θ V W κ) : IsKerSys θ W V (swapKer κ) where
  cont f := (h.cont f).comp continuous_swap
  left f γ hγ δ hδ g g' := h.left f δ hδ γ hγ g' g
  level f := by
    obtain ⟨U, U', hU, hU', hk⟩ := h.level f
    exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' => hk k' hk1' hk2' k hk1 hk2 g' g⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun f => ?_⟩
    obtain ⟨C, hC⟩ := hN f
    refine ⟨C, fun g g' => ?_⟩
    have hb := hC g' g
    rw [mul_comm (height θ V g' : ℝ)] at hb
    exact hb
  derV τ X hX f := by
    obtain ⟨f', hf'⟩ := h.derW τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  derW τ X hX f := by
    obtain ⟨f', hf'⟩ := h.derV τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  cap τ := by
    obtain ⟨a, b, ha, hb, hab⟩ := h.cap τ
    exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩

def constKer (V W : HSp D) : ℂ →ₗ[ℂ] (GA D V → GA D W → ℂ) where
  toFun c _ _ := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def OmCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w

def thKer (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GlobalTheory.RealWeil.thetaSub ψ S T →ₗ[ℂ] (GA D S → GA D T → ℂ) where
  toFun f g h := om (g, h) f.1 0
  map_add' f f' := by funext g h; simp
  map_smul' c f := by funext g h; simp

end GlobalTheory.Mem.Lift

end
