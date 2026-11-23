import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section
variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_map {S : Type} [CommRing S] {J : Ideal S} (φ : R →+* S) (h : I ≤ J.comap φ) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := fun N =>
  (hf N).comp (Ideal.quotientMap (J ^ N) φ ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow φ N)))

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x :=
  fun N => (hf N).mul (hg N)

private theorem ac_neg {f : Γ → R} (hf : AdicCont I f) : AdicCont I fun x => -f x :=
  fun N => (hf N).neg

private theorem ac_tn {f t : Γ → M2 R} (hf : ∀ i j, AdicCont I fun g => f g i j)
    (ht : ∀ i j, AdicCont I fun g => t g i j) (i j : Fin 4) : AdicCont I fun g => tn (f g) (t g) i j := by
  fin_cases i <;> fin_cases j <;> simp [tn] <;>
    first
    | exact ac_mul (hf _ _) (ht _ _)
    | exact ac_neg (ac_mul (hf _ _) (ht _ _))

end

theorem contOf4 : ContOf4 := by
  intro Ω _ _ _ l _ d T
  have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
  have hm : maximalIdeal d.c.O ≤ (maximalIdeal d.c₁.O).comap (inc d.h) := fun x hx =>
    (UpperTheory.V.Fr.sc_norm l d.c₁ (inc d.h x)).2.2 ((UpperTheory.V.Fr.sc_norm l d.c x).2.1 hx)
  have h1 : (d.Q T).Cont (maximalIdeal d.c₁.O) := fun i j N =>
    (ac_mul (ac_map (inc d.h) hm d.tw.cont) (ac_tn d.mod.cont d.tau.cont i j) N).comp_continuous hc
  exact ⟨h1, fun R _ f hf i j => ac_map (J := ⊥) f (fun y hy => Ideal.mem_comap.2 (Ideal.mem_bot.2 (hf y hy))) (h1 i j)⟩

end UpperTheory.V.Cu

end
