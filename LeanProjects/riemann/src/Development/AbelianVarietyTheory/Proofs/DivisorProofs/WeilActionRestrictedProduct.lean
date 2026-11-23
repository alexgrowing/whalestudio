import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdditiveCharacterProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisPure

variable {F : Type} [Field F] [NumberField F]

lemma evFin_int (z : AF F) : ∀ᶠ v in cofinite, evFin F v z ∈ v.adicCompletionIntegers F := z.2.2

lemma evFin_invOf_two (v : Pl F) {_ : Invertible (2 : Fv F v)} : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]

lemma evFin_phase {κ : Type} [Fintype κ] (v : Pl F) {_ : Invertible (2 : Fv F v)} (x a b : κ → AF F) :
    evFin F v (x ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b)) =
      (fun i => evFin F v (x i)) ⬝ᵥ (fun i => evFin F v (b i)) +
        ⅟(2 : Fv F v) * ((fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i))) := by
  simp only [dotProduct, map_add, map_mul, map_sum, evFin_invOf_two]

lemma trace_phase {κ : Type} [Fintype κ] (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b))) =
      GlobalTheory.ArchUniq.trP F κ (GlobalTheory.ArchUniq.locV x) (GlobalTheory.ArchUniq.locV b) +
        GlobalTheory.ArchUniq.trP F κ (GlobalTheory.ArchUniq.locV a) (GlobalTheory.ArchUniq.locV b) / 2 := by
  have h2 : ∀ z : AF F, evI F z = evI F (⅟(2 : AF F) * z) + evI F (⅟(2 : AF F) * z) := fun z => by
    simp only [GlobalTheory.ArchUniq.evI_eq_evIHom]
    rw [← map_add, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
  have hs : ∀ y c : κ → AF F, evI F (y ⬝ᵥ c) = ∑ i, GlobalTheory.ArchUniq.locV y i * GlobalTheory.ArchUniq.locV c i := fun y c => by
    simp only [dotProduct, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sum, map_mul, GlobalTheory.ArchUniq.locV]
  have hh : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (a ⬝ᵥ b))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (a ⬝ᵥ b)) / 2 := by
    rw [h2 (a ⬝ᵥ b), map_add]; ring
  rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_add, ← GlobalTheory.ArchUniq.evI_eq_evIHom, ← GlobalTheory.ArchUniq.evI_eq_evIHom, map_add, hh,
    hs, hs]
  rfl

end GlobalTheory.HeisPure

open GlobalTheory.HeisPure in

theorem GlobalTheory.HeisPure.rho_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) →
    (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    M.co.rho ψ u (pure f φ) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) (fun v => locOp v (M.co.rho ψ (partFin v u)) (φ v)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f φ hφ hstd
  classical
  have hunr := (GlobalTheory.PsiStdCond.psi_std_conductor F ψ hψ).1
  funext x

  have hfin1 : Function.HasFiniteMulSupport fun v : Pl F =>
      psiLoc ψ v (evFin F v (x ⬝ᵥ (M.co.e u).2 + ⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2))) := by
    have h := Filter.eventually_cofinite.1 (hunr.and (evFin_int (x ⬝ᵥ (M.co.e u).2 + ⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2))))
    refine h.subset fun v hv => ?_
    intro hP
    exact hv (GlobalTheory.AdeleCharProd.psiLoc_int hP.1 hP.2)
  have hfin2 : Function.HasFiniteMulSupport fun v : Pl F => φ v fun i => evFin F v ((x + (M.co.e u).1) i) := by
    have h := Filter.eventually_cofinite.1 (hstd.and (Filter.eventually_all.2 fun i => evFin_int ((x + (M.co.e u).1) i)))
    refine h.subset fun v hv => ?_
    intro hP
    apply hv
    show φ v (fun i => evFin F v ((x + (M.co.e u).1) i)) = 1
    rw [hP.1, Set.indicator_of_mem (show _ ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hP.2)]
    rfl
  have hprod : ∏ᶠ v, locOp v (M.co.rho ψ (partFin v u)) (φ v) (fun i => evFin F v (x i)) =
      (∏ᶠ v : Pl F, psiLoc ψ v (evFin F v (x ⬝ᵥ (M.co.e u).2 + ⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)))) *
        ∏ᶠ v, φ v fun i => evFin F v ((x + (M.co.e u).1) i) := by
    rw [← finprod_mul_distrib hfin1 hfin2]
    refine finprod_congr fun v => ?_
    rw [(locOp_rho M.co hψ.1 v u (hφ v)).2]
    change GlobalTheory.LatVac.psiAt ψ v _ * φ v _ = _
    rw [GlobalTheory.LatVac.psiAt_apply]
    congr 2
    exact (evFin_phase v x (M.co.e u).1 (M.co.e u).2).symm
  calc M.co.rho ψ u (pure f φ) x
      = ψ (x ⬝ᵥ (M.co.e u).2 + ⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) *
          (f (fun i => evI F ((x + (M.co.e u).1) i)) * ∏ᶠ v, φ v fun i => evFin F v ((x + (M.co.e u).1) i)) := rfl
    _ = Complex.exp (-(2 * Real.pi * Complex.I) * ((GlobalTheory.ArchUniq.trP F (Fin n × Fin d) (GlobalTheory.ArchUniq.locV x)
            (GlobalTheory.ArchUniq.locV (M.co.e u).2) + GlobalTheory.ArchUniq.trP F (Fin n × Fin d) (GlobalTheory.ArchUniq.locV (M.co.e u).1)
            (GlobalTheory.ArchUniq.locV (M.co.e u).2) / 2 : ℝ) : ℂ)) * f (GlobalTheory.ArchUniq.locV x + GlobalTheory.ArchUniq.locV (M.co.e u).1) *
          ((∏ᶠ v : Pl F, psiLoc ψ v (evFin F v (x ⬝ᵥ (M.co.e u).2 + ⅟(2 : AF F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)))) *
            ∏ᶠ v, φ v fun i => evFin F v ((x + (M.co.e u).1) i)) := by
      rw [GlobalTheory.AdeleCharProd.psi_eq_inf_mul_finprod F ψ hψ hunr, trace_phase]
      have hx : (fun i => evI F ((x + (M.co.e u).1) i)) = GlobalTheory.ArchUniq.locV x + GlobalTheory.ArchUniq.locV (M.co.e u).1 := by
        funext i
        simp only [Pi.add_apply, GlobalTheory.ArchUniq.locV, GlobalTheory.ArchUniq.evI_eq_evIHom, map_add]
      rw [hx]
      ring
    _ = pure (locOpInf (M.co.rho ψ (partInf F u)) f) (fun v => locOp v (M.co.rho ψ (partFin v u)) (φ v)) x := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, (locOpInf_rho M.co hψ u f).2, hprod]
      rfl
