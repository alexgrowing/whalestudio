import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem qdet_fin_two {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V) (u : ℂ) :
    Formalism.REAL.qdet X u = (algebraMap ℂ (Module.End ℂ V) u + X 0 0) * (algebraMap ℂ (Module.End ℂ V) (u - 1) + X 1 1) - X 1 0 * X 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, hp, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem four_qdet {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (u : ℂ) (w : V) :
    (4 : ℂ) • Formalism.REAL.qdet X u w = ((2 * u - 1) ^ 2 - 1) • w + (2 * (2 * u - 1)) • (X 0 0 + X 1 1) w
      + (X 0 0 + X 1 1) ((X 0 0 + X 1 1) w)
      - ((X 0 0 - X 1 1) ((X 0 0 - X 1 1) w) + (2 : ℂ) • (X 0 1 (X 1 0 w) + X 1 0 (X 0 1 w))) := by
  have r1 : X 0 0 (X 1 1 w) - X 1 1 (X 0 0 w) = 0 := by
    simpa using LinearMap.congr_fun (hX 0 0 1 1) w
  have r2 : X 0 1 (X 1 0 w) - X 1 0 (X 0 1 w) = X 0 0 w - X 1 1 w := by
    simpa using LinearMap.congr_fun (hX 0 1 1 0) w
  rw [qdet_fin_two]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add,
    map_sub, map_smul]
  linear_combination (norm := module) (2 : ℂ) • r1 + (2 : ℂ) • r2

theorem UpperTheory.ConvolutionTheory.R2.Fo.capAbs :
    ∀ (V S T : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    (V₀ : Submodule ℂ V) (S₀ : Submodule ℂ S) (Λ : V →ₗ[ℂ] S →ₗ[ℂ] T) (E : Fin 2 → Fin 2 → Module.End ℂ V) (P : Fin 2 → Fin 2 → Module.End ℂ T)
    (a : Fin 2 → Fin 2 → Module.End ℂ S) (e f h : Module.End ℂ S), Formalism.REAL.GlRel E → Formalism.REAL.GlRel P →
    (∀ i j, ∀ v ∈ V₀, E i j v ∈ V₀) → (∀ i j, ∀ s ∈ S₀, a i j s ∈ S₀) → (∀ s ∈ S₀, e s ∈ S₀) → (∀ s ∈ S₀, f s ∈ S₀) →
    (∀ i j, ∀ v ∈ V₀, ∀ s ∈ S₀, P i j (Λ v s) = Λ v (a i j s) + if i = j then Λ (E 1 1 v) s else 0) →
    (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e s) = -Λ (E 0 1 v) s) → (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f s) = -Λ (E 1 0 v) s) →
    e * f - f * e = h → a 0 0 + a 1 1 = -h →
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h + 2 * (e * f + f * e) →
    ∀ u, ∀ v ∈ V₀, ∀ s ∈ S₀, Formalism.REAL.qdet P u (Λ v s) = Λ (Formalism.REAL.qdet E u v) s := by
  intro V S T _ _ _ _ _ _ V₀ S₀ Λ E P a e f h hE hP hEV haS heS hfS hPΛ heΛ hfΛ hh hz hb u v hv s hs
  have hH : ∀ w, E 0 1 (E 1 0 w) - E 1 0 (E 0 1 w) = (E 0 0 - E 1 1) w := fun w => by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) w
  have hef : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e (f s)) = Λ (E 1 0 (E 0 1 v)) s := fun v hv s hs => by
    rw [heΛ v hv _ (hfS s hs), hfΛ _ (hEV 0 1 v hv) s hs, neg_neg]
  have hfe : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f (e s)) = Λ (E 0 1 (E 1 0 v)) s := fun v hv s hs => by
    rw [hfΛ v hv _ (heS s hs), heΛ _ (hEV 1 0 v hv) s hs, neg_neg]
  have hhS : ∀ s ∈ S₀, h s ∈ S₀ := fun s hs => by
    rw [← hh]
    exact S₀.sub_mem (heS _ (hfS s hs)) (hfS _ (heS s hs))
  have hHV : ∀ v ∈ V₀, (E 0 0 - E 1 1) v ∈ V₀ := fun v hv =>
    V₀.sub_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hZV : ∀ v ∈ V₀, (E 0 0 + E 1 1) v ∈ V₀ := fun v hv =>
    V₀.add_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hhΛ : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (h s) = -Λ ((E 0 0 - E 1 1) v) s := fun v hv s hs => by
    rw [← hh, ← hH v, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hef v hv s hs,
      hfe v hv s hs, map_sub, LinearMap.sub_apply, neg_sub]
  have hZ : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 + P 1 1) (Λ v s) = Λ ((E 0 0 + E 1 1) v) s := fun v hv s hs => by
    have h1 : a 0 0 s + a 1 1 s = -h s := by simpa using LinearMap.congr_fun hz s
    have h2 : Λ v (a 0 0 s) + Λ v (a 1 1 s) = Λ ((E 0 0 - E 1 1) v) s := by
      rw [← map_add, h1, map_neg, hhΛ v hv s hs, neg_neg]
    simp only [LinearMap.add_apply, hPΛ _ _ v hv s hs, if_true, map_add]
    simp only [LinearMap.sub_apply, map_sub] at h2
    linear_combination (norm := module) h2
  have hHP : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 - P 1 1) (Λ v s) = Λ v ((a 0 0 - a 1 1) s) := fun v hv s hs => by
    simp only [LinearMap.sub_apply, hPΛ _ _ v hv s hs, if_true, map_sub]
    abel
  have hA : ∀ s ∈ S₀, (a 0 0 - a 1 1) s ∈ S₀ := fun s hs => S₀.sub_mem (haS 0 0 s hs) (haS 1 1 s hs)
  have hBr : (P 0 0 - P 1 1) ((P 0 0 - P 1 1) (Λ v s)) + (2 : ℂ) • (P 0 1 (P 1 0 (Λ v s)) + P 1 0 (P 0 1 (Λ v s)))
      = Λ ((E 0 0 - E 1 1) ((E 0 0 - E 1 1) v) + (2 : ℂ) • (E 0 1 (E 1 0 v) + E 1 0 (E 0 1 v))) s := by
    have p10 : P 1 0 (Λ v s) = Λ v (a 1 0 s) := by simpa using hPΛ 1 0 v hv s hs
    have p01 : P 0 1 (Λ v s) = Λ v (a 0 1 s) := by simpa using hPΛ 0 1 v hv s hs
    have p01' : P 0 1 (Λ v (a 1 0 s)) = Λ v (a 0 1 (a 1 0 s)) := by
      simpa using hPΛ 0 1 v hv _ (haS 1 0 s hs)
    have p10' : P 1 0 (Λ v (a 0 1 s)) = Λ v (a 1 0 (a 0 1 s)) := by
      simpa using hPΛ 1 0 v hv _ (haS 0 1 s hs)
    have hb' : (a 0 0 - a 1 1) ((a 0 0 - a 1 1) s) + (2 : ℂ) • (a 0 1 (a 1 0 s) + a 1 0 (a 0 1 s))
        = h (h s) + (2 : ℂ) • (e (f s) + f (e s)) := by
      have := LinearMap.congr_fun hb s
      simp only [two_mul, LinearMap.add_apply, Module.End.mul_apply] at this
      rw [two_smul, two_smul]
      exact this
    rw [hHP v hv s hs, hHP v hv _ (hA s hs), p10, p01, p01', p10', ← map_add, ← map_smul, ← map_add, hb', map_add, map_smul,
      map_add, hef v hv s hs, hfe v hv s hs, hhΛ v hv _ (hhS s hs), hhΛ _ (hHV v hv) s hs, neg_neg,
      map_add, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.add_apply, add_comm (Λ (E 1 0 _) s)]
  have key : (4 : ℂ) • Formalism.REAL.qdet P u (Λ v s) = (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s := by
    have k2 : (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s = Λ ((4 : ℂ) • Formalism.REAL.qdet E u v) s := by
      rw [map_smul, LinearMap.smul_apply]
    rw [k2, four_qdet P hP u, four_qdet E hE u v, hBr, hZ v hv s hs, hZ _ (hZV v hv) s hs]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  exact smul_right_injective T (by norm_num : (4 : ℂ) ≠ 0) key
