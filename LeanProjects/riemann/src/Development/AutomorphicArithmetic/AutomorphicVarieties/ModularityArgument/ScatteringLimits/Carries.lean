import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits

noncomputable section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology
open scoped InnerProductSpace

namespace UpperTheory.V.Z.IntegralApplyAeEq

structure Flow (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : ℝ → H →L[ℂ] H
  zero : ∀ h, U 0 h = h
  add : ∀ s t h, U (s + t) h = U s (U t h)
  norm : ∀ t h, ‖U t h‖ = ‖h‖
  cont : ∀ h, Continuous fun t => U t h

namespace Flow

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : Flow H)

def rev : Flow H where
  U t := F.U (-t)
  zero h := by simpa using F.zero h
  add s t h := by rw [neg_add, F.add]
  norm t h := F.norm _ h
  cont h := (F.cont h).comp continuous_neg

def av (ψ : ℝ → ℂ) : H →L[ℂ] H := Classical.epsilon fun A : H →L[ℂ] H => ∀ h, A h = ∫ t, ψ t • F.U t h

def Cob (h : H) : Prop := ∃ k : H, ∀ t : ℝ, ∫ s in (0 : ℝ)..t, F.U s h = F.U t k - k

def Null : Prop :=
  ∀ h h' : H, Tendsto (fun t => ⟪h', F.U t h⟫_ℂ) atTop (𝓝 0) ∧ Tendsto (fun t => ⟪h', F.U t h⟫_ℂ) atBot (𝓝 0)

end Flow

def wR (t : ℝ) : ℂ := (Iic (0 : ℝ)).indicator (fun t => (Real.exp t : ℂ)) t

structure Bump (ψ : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : Continuous ψ
  nonneg : ∀ t, 0 ≤ ψ t
  le : ∀ t, ψ t ≤ 2 / (b - a)
  supp : ∀ t, t ∉ Icc a b → ψ t = 0
  total : ∫ t, ψ t = 1

section Line

variable (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def sh (t : ℝ) : L V →L[ℂ] L V :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + t) (measurePreserving_add_right volume t)).toContinuousLinearMap

theorem sh_ae (t : ℝ) (u : L V) : ∀ᵐ x : ℝ, sh V t u x = u (x + t) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume t)

def shF : Flow (L V) where
  U := sh V
  zero h := Lp.ext ((sh_ae V 0 h).mono fun x hx => by simpa using hx)
  add s t h := Lp.ext (by
    filter_upwards [sh_ae V (s + t) h, sh_ae V s (sh V t h),
      (measurePreserving_add_right volume s).quasiMeasurePreserving.ae (sh_ae V t h)] with x h1 h2 h3
    rw [h1, h2, h3, add_assoc])
  norm t h := (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + t) (measurePreserving_add_right volume t)).norm_map h
  cont h := Continuous.compMeasurePreservingLp (f := fun _ : ℝ => h) (g := fun t : ℝ => (⟨fun x => x + t, by fun_prop⟩ : C(ℝ, ℝ)))
    continuous_const (ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add continuous_fst))
    (fun t => measurePreserving_add_right volume t) (by simp)

def cut (s : Set ℝ) : L V →L[ℂ] L V := Classical.epsilon fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x

def sv (φ : ℝ → ℂ) : V →L[ℂ] L V := Classical.epsilon fun C : V →L[ℂ] L V => ∀ e, ∀ᵐ x : ℝ, C e x = φ x • e

def one : V →L[ℂ] L V := sv V ((Ioc (0 : ℝ) 1).indicator fun _ => 1)

variable {V}

def Bdd (p : L V) : Prop := ∃ ρ : ℝ, cut V (Icc (-ρ) ρ) p = p

def Tail (p : L V) : Prop := ∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ‖cut V (Icc (-ρ) ρ)ᶜ p‖ ≤ C * Real.exp (-ρ)

def WLe (c : ℝ) (p : L V) (Q : ℝ) : Prop :=
  Integrable (fun x => Real.exp (c * x) * ‖p x‖ ^ 2) ∧ ∫ x, Real.exp (c * x) * ‖p x‖ ^ 2 ≤ Q ^ 2

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def conv (κ : ℝ → V →L[ℂ] W) : L V →L[ℂ] L W :=
  Classical.epsilon fun C : L V →L[ℂ] L W => ∀ u, ∀ᵐ x : ℝ, C u x = ∫ t : ℝ, κ t (u (x + t))

def kv (κ : ℝ → V →L[ℂ] W) : V →L[ℂ] L W := Classical.epsilon fun C : V →L[ℂ] L W => ∀ e, ∀ᵐ x : ℝ, C e x = κ (-x) e

def sharp [CompleteSpace V] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (t : ℝ) : W →L[ℂ] V := ContinuousLinearMap.adjoint (κ (-t))

def scal (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ψ : ℝ → ℂ) (t : ℝ) : V →L[ℂ] V := ψ t • ContinuousLinearMap.id ℂ V

end Line

structure Sc (H V W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] where
  J : L V ≃ₗᵢ[ℂ] H
  J' : L W ≃ₗᵢ[ℂ] H
  F : Flow H
  T₀ : ℝ
  hJ : ∀ t u, F.U t (J u) = J (sh V t u)
  hJ' : ∀ t v, F.U t (J' v) = J' (sh W (-t) v)
  causal : ∀ (s : ℝ) (u : L V) (v : L W), ⟪J (cut V (Ioi s) u), J' (cut W (Ioi (2 * T₀ - s)) v)⟫_ℂ = 0

namespace Sc

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)

def swap : Sc H W V where
  J := M.J'
  J' := M.J
  F := M.F.rev
  T₀ := M.T₀
  hJ t u := by simpa [Flow.rev] using M.hJ' (-t) u
  hJ' t v := M.hJ (-t) v
  causal s u v := by
    have h := M.causal (2 * M.T₀ - s) v u
    rw [sub_sub_cancel] at h
    rw [← inner_conj_symm, h, map_zero]

def P (s : Set ℝ) : H →L[ℂ] H :=
  (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L cut V s ∘L (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)

def P' (s : Set ℝ) : H →L[ℂ] H := M.swap.P s

def abelian₂ (T T' : ℝ) : H →L[ℂ] H := 1 - M.P (Ioi T) - M.P' (Ioi T')

def Carries (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) : Prop := ∀ u, X (M.J u) = M.J' (conv κ u)

def Acts (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) : Prop :=
  (∀ u, Y (M.J u) = M.J (conv β u)) ∧ ∀ v, Y (M.J' v) = M.J' (conv β' v)

def IsN (N : W →ₗ[ℂ] V) : Prop := ∀ w, M.F.Cob (M.J' (one W w) - M.J (one V (N w)))

def cor (φ : ℝ → ℂ) (e : V) (p : L W) (s : ℝ) : ℂ := ⟪M.J (sv V φ e), M.F.U s (M.J' p)⟫_ℂ

end Sc

end UpperTheory.V.Z.IntegralApplyAeEq
