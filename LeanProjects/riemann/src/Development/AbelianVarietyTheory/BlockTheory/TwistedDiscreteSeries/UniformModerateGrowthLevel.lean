import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar}

def IsHolPar (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ, ∃ (p q : ℕ) (κ : Fin p ⊕ Fin q → ℤ), Formalism.L2.NTheta.HolOK p q κ ∧ S τ = Formalism.L2.NTheta.holPar p q κ

def pMinus (M : DSModel W S) (τ : D.what₂.Tau) : Set (Matrix (Fin W.rank) (Fin W.rank) ℂ) :=
  {Z | ∀ a b, ¬ (M.ε τ a = false ∧ M.ε τ b = true) → (M.fr τ * Z * (M.fr τ)⁻¹) a b = 0}

abbrev KMap (M : DSModel W S) : Type :=
  MultilinearMap ℂ (fun τ : D.what₂.Tau => lowT M τ) (GA D W → ℂ)

variable (W) in

structure IsLevel (J : Subgroup (GA D W)) (χ : GA D W → ℂ) : Prop where
  fin : J ≤ GfC W
  opn : ∃ O : Subgroup (GA D W), IsOpen (O : Set (GA D W)) ∧ ∀ k ∈ O, k ∈ GfC W → k ∈ J
  mul : ∀ k ∈ J, ∀ k' ∈ J, χ (k * k') = χ k * χ k'
  unit : ∀ k ∈ J, ‖χ k‖ = 1

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

variable (W) in

def IsSmoothFn (φ : GA D W → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin W.rank) (Fin W.rank) ℂ),
    (∀ i, Xs i ∈ lieAt W (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ W (τs i) (Xs i) (t i)).prod)

variable (W) in

def IsUnifModGrowth (φ : GA D W → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt W p.1) →
    ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC W,
      ‖(l.foldr (fun p f => Rder θ W p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ W g ^ N

open Classical in

structure IsHolCuspKMap (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ) (U : KMap M) : Prop where
  cont : ∀ e, Continuous (U e)
  left : ∀ e, ∀ γ ∈ GQ W, ∀ g, U e (γ * g) = U e g
  lev : ∀ e, ∀ k ∈ J, ∀ g, U e (g * k) = χ k * U e g
  smooth : ∀ e, IsSmoothFn W θ (U e)
  growth : ∀ e, IsUnifModGrowth W θ (U e)
  cusp : ∀ e, IsCuspFun W (U e)
  equiv : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (e : ∀ τ', lowT M τ') (w : lowT M τ),
    ((w : M.sm τ) : M.H τ) = M.σ τ k ((e τ : M.sm τ) : M.H τ) →
      U (Function.update e τ w) = rTr W (atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (U e)
  hol : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ e, RderC θ W τ Z (U e) = 0

def RestrictsTo (M : DSModel W S) (T : MMap M) (U : KMap M) : Prop :=
  ∀ e : ∀ τ, lowT M τ, T (fun τ => (e τ : M.sm τ)) = U e

def HolExtend : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (W : HSp D) (S : D.what₂.Tau → SPar), IsHolPar S →
    ∀ (M : DSModel W S) (J : Subgroup (GA D W)) (χ : GA D W → ℂ), IsLevel W J χ →
    ∀ U : KMap M, IsHolCuspKMap θ M (J : Set (GA D W)) χ U →
      ∃ T : MMap M, IsMultMap θ M (J : Set (GA D W)) χ T ∧ RestrictsTo M T U

theorem mem_mult {M : DSModel W S} {J : Set (GA D W)} {χ : GA D W → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T) :
    T ∈ Mult θ M J χ := Submodule.subset_span h

theorem isHolPar_parW (κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ)
    (h : ∀ τ, Formalism.L2.NTheta.HolOK _ _ (κ τ)) : IsHolPar (parW W κ) :=
  fun τ => ⟨_, _, κ τ, h τ, rfl⟩

theorem single_mem_pMinus (M : DSModel W S) (τ : D.what₂.Tau) {a b : Fin W.rank} (ha : M.ε τ a = false)
    (hb : M.ε τ b = true) : (M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ ∈ pMinus M τ := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h : M.fr τ * ((M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ) * (M.fr τ)⁻¹ = Matrix.single a b 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  intro c d hcd
  rw [h, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd ⟨ha, hb⟩

theorem isLevel_top : IsLevel W (GfC W) (fun _ => 1) :=
  ⟨le_rfl, ⟨⊤, by simp, fun _ _ h => h⟩, fun _ _ _ _ => by simp, fun _ _ => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

end
