import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivArch

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_heisD {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f
      (heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  intro r hr x
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV (F := F) y) := by
  intro a ha
  funext i
  refine Prod.ext ?_ ?_
  · have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
    show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    exact mul_zero _

end GlobalTheory.HeisDerivArch

open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch in

theorem GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ ∀ f g : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) ⇑f ⇑g → ∀ y, g y =
        fderiv ℝ (⇑f) y v.1 - 2 * Real.pi * Complex.I * (trP F (Fin n × Fin d) y v.2 : ℂ) * f y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  have heu : M.co.e u = (liftV v.1, liftV v.2) := by rw [hu, LinearEquiv.apply_symm_apply]
  refine ⟨u, ?_, ?_⟩
  · intro a ha
    have e1 : a • u = M.co.e.symm (a • (liftV v.1, liftV v.2)) := by rw [hu, map_smul]
    rw [e1, Prod.smul_mk, at_liftV v.1 a ha, at_liftV v.2 a ha, Prod.mk_zero_zero, map_zero]
  · intro f g hg y
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
    have hr := hR f
    set x : Fin n × Fin d → AF F := liftV y with hx
    have hd1 := hg R hr x
    have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
    have huniq := hd1.unique hd2
    have hRx : R x = R 0 := by
      have := hr.1 0 x (at_liftV y)
      rwa [zero_add] at this
    have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
    simp only [tens, hlx, hRx] at huniq
    have huniq' := mul_right_cancel₀ hR0 huniq
    rw [huniq', heisD_apply, mult_apply, heu]
    have hv1 : (fun i => evI F ((liftV (F := F) v.1) i)) = v.1 := Coord.loc_lift v.1
    simp only [hv1, trForm_apply]
    have hv2 : ∀ i, evI F ((liftV (F := F) v.2) i) = v.2 i := fun i => congrFun (Coord.loc_lift v.2) i
    simp only [hv2, trP]
    ring
