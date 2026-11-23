import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schOfClosed :
    UpperTheory.V.Af.Smo.SchOfClosed := by
  intro X _ _ _ A hA
  have b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ X) → (X →L[ℝ] ℝ), ∀ i x, c i x = b.repr x i :=
    ⟨fun i => LinearMap.toContinuousLinearMap (b.coord i), fun i x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin (Module.finrank ℝ X) → (ℂ →L[ℝ] (X →L[ℝ] ℂ)),
      ∀ i z v, L i z v = c i v • z :=
    ⟨fun i => ContinuousLinearMap.smulRightL ℝ X ℂ (c i), fun i z v => rfl⟩
  have hsm : ∀ n : ℕ, ∀ f ∈ A, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero => intro f hf; exact contDiff_zero.2 (hA f hf).2.1.continuous
    | succ n ih =>
      intro f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨(hA f hf).2.1, by simp, ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      exact ih _ ((hA f hf).2.2.1 v)
  have hinf : ∀ f ∈ A, ContDiff ℝ ∞ f := fun f hf => contDiff_infty.2 fun n => hsm n f hf
  have hx : ∀ x : X, ‖x‖ ≤ ∑ i, ‖b i‖ * ‖c i x‖ := by
    intro x
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ = ∑ i, ‖b i‖ * ‖c i x‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, hc, mul_comm]
  have h0 : ∀ k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro f hf
      obtain ⟨C, hC⟩ := (hA f hf).1
      exact ⟨C, fun x => by simpa using hC x⟩
    | succ k ih =>
      intro f hf
      choose C hC using fun i => ih _ ((hA f hf).2.2.2 (c i))
      refine ⟨∑ i, ‖b i‖ * C i, fun x => ?_⟩
      calc ‖x‖ ^ (k + 1) * ‖f x‖ = ‖x‖ * (‖x‖ ^ k * ‖f x‖) := by ring
        _ ≤ (∑ i, ‖b i‖ * ‖c i x‖) * (‖x‖ ^ k * ‖f x‖) := by gcongr; exact hx x
        _ = ∑ i, ‖b i‖ * (‖x‖ ^ k * ‖(↑(c i x) : ℂ) * f x‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real]
            ring
        _ ≤ ∑ i, ‖b i‖ * C i := by
            gcongr with i
            exact hC i x
  have hd : ∀ n k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      intro k f hf
      obtain ⟨C, hC⟩ := h0 k f hf
      exact ⟨C, fun x => by rw [norm_iteratedFDeriv_zero]; exact hC x⟩
    | succ n ih =>
      intro k f hf
      obtain ⟨g, hg⟩ : ∃ g : Fin (Module.finrank ℝ X) → X → ℂ, ∀ i x, g i x = fderiv ℝ f x (b i) :=
        ⟨fun i x => fderiv ℝ f x (b i), fun _ _ => rfl⟩
      have hgA : ∀ i, g i ∈ A := by
        intro i
        have : g i = fun x => fderiv ℝ f x (b i) := funext (hg i)
        rw [this]
        exact (hA f hf).2.2.1 (b i)
      have hfd : fderiv ℝ f = fun x => ∑ i, L i (g i x) := by
        funext x
        ext v
        rw [ContinuousLinearMap.sum_apply]
        simp only [hL, hg, hc]
        conv_lhs => rw [← b.sum_repr v]
        rw [map_sum]
        simp only [map_smul]
      have hsum : iteratedFDeriv ℝ n (fun x => ∑ i, L i (g i x))
          = ∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) :=
        iteratedFDeriv_sum (f := fun i y => L i (g i y)) (u := Finset.univ)
          (fun i _ => (L i).contDiff.comp (hsm n _ (hgA i)))
      choose C hC using fun i => ih k (g i) (hgA i)
      refine ⟨∑ i, ‖L i‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd, hsum, Finset.sum_apply]
      calc ‖x‖ ^ k * ‖∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖
          ≤ ‖x‖ ^ k * ∑ i, ‖iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖ := by
            gcongr
            exact norm_sum_le _ _
        _ ≤ ‖x‖ ^ k * ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (g i) x‖ := by
            gcongr with i
            exact (L i).norm_iteratedFDeriv_comp_left (hsm n _ (hgA i)).contDiffAt le_rfl
        _ = ∑ i, ‖L i‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g i) x‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, ‖L i‖ * C i := by
            gcongr with i
            exact hC i x
  intro f hf
  exact ⟨⟨f, hinf f hf, fun k n => hd n k f hf⟩, rfl⟩
