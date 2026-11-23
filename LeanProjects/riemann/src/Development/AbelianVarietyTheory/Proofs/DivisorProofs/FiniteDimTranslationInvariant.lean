import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TransODE

open NormedSpace

theorem linear_ode_eq_exp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (y : ℝ → E) (hy : ∀ s, HasDerivAt y (L (y s)) s) (t : ℝ) :
    y t = exp (t • L) (y 0) := by
  let z : ℝ → E := fun s => exp ((t - s) • L) (y s)
  have hd : ∀ s, HasDerivAt z 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • L)) (exp ((t - s) • L) * L) (t - s) :=
      hasDerivAt_exp_smul_const L (t - s)
    have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    have h4 := h3.clm_apply (hy s)
    convert h4 using 1
    · rfl
    · simp [Function.comp_def]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [z] using hc

theorem mem_of_translate (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G)
    (hfin : FiniteDimensional ℂ W) (hγ : γ 0 = 1)
    (hder : ∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) :
    ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W := by
  classical
  let d := Module.finrank ℂ W
  let b : Module.Basis (Fin d) ℂ W := Module.finBasis ℂ W
  have hb : ∀ i, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => (b i : G → ℂ) (γ τ * g)) (ψ' (γ t * g)) t :=
    fun i => hder _ (b i).2
  choose D hDW hD using hb
  have hexp : ∀ (w : W) (x : G), (w : G → ℂ) x = ∑ j, b.repr w j * (b j : G → ℂ) x := by
    intro w x
    calc (w : G → ℂ) x = ((∑ j, b.repr w j • b j : W) : G → ℂ) x := by rw [b.sum_repr w]
      _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => b.repr ⟨D i, hDW i⟩ j
  have hM : ∀ i x, D i x = ∑ j, M i j * (b j : G → ℂ) x := fun i x => hexp ⟨D i, hDW i⟩ x
  let Lc : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  let L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) := Lc.restrictScalars ℝ
  have hL : ∀ v i, L v i = ∑ j, M i j * v j := by
    intro v i; simp [L, Lc, Matrix.mulVec, dotProduct]
  have hLc : ∀ (c : ℂ) v, L (c • v) = c • L v := fun c v => by simp [L]
  have hLs : ∀ (f : Fin d → (Fin d → ℂ)), L (∑ j, f j) = ∑ j, L (f j) := fun f => map_sum L f _
  have key : ∀ (g : G) (t : ℝ) i, (b i : G → ℂ) (γ t * g) =
      ∑ j, (exp (t • L) (Pi.single j 1)) i * (b j : G → ℂ) g := by
    intro g t i
    let y : ℝ → (Fin d → ℂ) := fun s k => (b k : G → ℂ) (γ s * g)
    have hy : ∀ s, HasDerivAt y (L (y s)) s := by
      intro s
      rw [hasDerivAt_pi]
      intro k
      have := hD k g s
      rw [hM] at this
      simpa [y, hL] using this
    let v : Fin d → ℂ := fun j => (b j : G → ℂ) g
    let y2 : ℝ → (Fin d → ℂ) := fun s => ∑ j, v j • exp (s • L) (Pi.single j 1)
    have hy2 : ∀ s, HasDerivAt y2 (L (y2 s)) s := by
      intro s
      have : HasDerivAt y2 (∑ j, v j • (L * exp (s • L)) (Pi.single j 1)) s := by
        have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun j s => v j • exp (s • L) (Pi.single j 1))
          (A' := fun j => v j • (L * exp (s • L)) (Pi.single j 1)) (x := s) (fun j _ =>
            (((hasDerivAt_exp_smul_const' L s).clm_apply (hasDerivAt_const s (Pi.single j (1:ℂ) : Fin d → ℂ))).const_smul (v j)).congr_deriv (by simp))
        simpa [y2] using this
      convert this using 1
      simp [y2, hLs, hLc, ContinuousLinearMap.mul_apply]
    have e1 := GlobalTheory.TransODE.linear_ode_eq_exp L y hy t
    have e2 := GlobalTheory.TransODE.linear_ode_eq_exp L y2 hy2 t
    have h0 : y 0 = y2 0 := by
      funext k
      simp [y, y2, v, hγ, Pi.single_apply]
    have := congrFun (e1.trans (h0 ▸ e2.symm)) i
    simpa [y, y2, v, mul_comm, Finset.sum_apply] using this
  intro ψ hψ t
  have hfun : (fun g => ψ (γ t * g)) = ∑ i, b.repr ⟨ψ, hψ⟩ i •
      ∑ j, (exp (t • L) (Pi.single j 1)) i • (b j : G → ℂ) := by
    funext g
    have := hexp ⟨ψ, hψ⟩ (γ t * g)
    simp only at this
    rw [this]
    simp [key, Finset.sum_apply, Finset.mul_sum]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)

theorem main : ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G), FiniteDimensional ℂ W → γ 0 = 1 → (∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ), HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) → ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W :=
  fun G _ W γ hfin hγ hder => mem_of_translate G W γ hfin hγ hder

end GlobalTheory.TransODE
