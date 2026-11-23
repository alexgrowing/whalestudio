import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def kFin (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.H τ) :=
  GlobalTheory.KFiniteVectors.kFiniteVectors (M.ε τ) (M.σ τ)

abbrev KVec (M : DSModel V S) : Type := ∀ τ : D.what₂.Tau, kFin M τ

abbrev KMap (M : DSModel V S) : Type := MultilinearMap ℂ (fun τ : D.what₂.Tau => kFin M τ) (GA D V → ℂ)

def maxCpt (M : DSModel V S) (τ : D.what₂.Tau) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)}

open Classical in

def IsGKMap (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : KMap M) : Prop :=
  (∀ u, IsAutFun V (T₀ u)) ∧
  (∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) ∧
  (∀ u, IsCuspFun V (T₀ u)) ∧
  (∀ u, MemLp (T₀ u) 2 (μ.restrict 𝓕)) ∧
  (∀ u, GlobalTheory.Grow.UnifModGrowth V θ (T₀ u)) ∧
  (∀ u, ∀ k ∈ J, ∀ g, T₀ u (g * k) = χ k * T₀ u g) ∧
  (∀ τ, ∀ k ∈ maxCpt M τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = M.rep τ k (u τ) →
    T₀ (Function.update u τ w) = rTr V (atTau θ V τ k) (T₀ u)) ∧
  (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = dRep (M.rep τ) X (u τ) →
    T₀ (Function.update u τ w) = Rder θ V τ X (T₀ u))

def Extends {M : DSModel V S} (T : MMap M) (T₀ : KMap M) : Prop :=
  ∀ (v : M.Vec) (u : KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u

def ExtExists (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ T₀ : KMap M, IsGKMap θ M J χ μ 𝓕 T₀ → ∃! T : MMap M, IsMultMap θ M J χ T ∧ Extends T T₀

def RestrInj (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ kFin M τ) → T v = 0) → T = 0

def GKExtension (D : D7) : Prop := ExtExists D ∧ RestrInj D

theorem maxCpt_subset (M : DSModel V S) (τ : D.what₂.Tau) : maxCpt M τ ⊆ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  intro g hg
  have h1 : (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc _ (Formalism.REAL.Jm (M.ε τ)), ← hg.2, ← Matrix.mul_assoc]
    have := (Matrix.mem_unitaryGroup_iff').1 hg.1
    rw [Matrix.star_eq_conjTranspose] at this
    rw [this, Matrix.one_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have e : M.fr τ * g * (M.fr τ)⁻¹ * M.fr τ = M.fr τ * g := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  show gᴴ * gramAt D V τ * g = gramAt D V τ
  rw [← M.fr_gram τ]
  calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
      = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)) * M.fr τ := by
        conv_lhs => rw [← e]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]

theorem rep_mem_kFin (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ)
    {v : M.H τ} (hv : v ∈ kFin M τ) : M.rep τ k v ∈ kFin M τ := by
  obtain ⟨A, hA, ha, hs⟩ := hv
  exact ⟨A, hA, hs _ hk v ha, hs⟩

theorem kFin_ne_bot (M : DSModel V S) (τ : D.what₂.Tau) : kFin M τ ≠ ⊥ := by
  obtain ⟨A, hA, hs, -, ⟨v, hv, h0, -⟩, -⟩ := (M.ds τ).2.2.2.2.2.1
  exact fun h => h0 ((Submodule.mem_bot ℂ).1 (h ▸ (show v ∈ kFin M τ from ⟨A, hA, hv, hs⟩)))

example (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) : IsGKMap θ M J χ μ 𝓕 0 := by
  refine ⟨fun _ => ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, fun _ => zero_mem _,
    fun _ _ _ _ _ _ _ _ _ => by simp, fun _ => MemLp.zero, fun _ => ⟨0, fun l _ => ⟨0, fun g => ?_⟩⟩,
    fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => ?_⟩
  · have : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ),
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := fun l => by
      induction l with
      | nil => rfl
      | cons p l ih => rw [List.foldr_cons, ih]; funext g; simp [Rder]
    rw [MultilinearMap.zero_apply, this]
    simp
  · funext g
    simp [Rder]

end GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

end
