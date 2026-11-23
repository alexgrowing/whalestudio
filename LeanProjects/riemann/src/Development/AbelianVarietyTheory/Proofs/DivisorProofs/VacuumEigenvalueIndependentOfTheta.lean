import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacThetaInd

theorem psi_half_symp_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have ht : cA σ (hTens (cA σ) (incM F X.J) (incM F W.J) γ γ) = -hTens (cA σ) (incM F X.J) (incM F W.J) γ γ :=
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (fun i j => by simp only [incM, Matrix.map_apply, hi, hX.herm])
      (fun i j => by simp only [incM, Matrix.map_apply, hi, hW.skew, map_neg]) γ γ
  set t := hTens (cA σ) (incM F X.J) (incM F W.J) γ γ with htdef
  have htr : ∀ z, Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
    GlobalTheory.VacCocycle.trace_conj (cA σ) hc
  set a := inclR (F := F) (AF F) (θ : E) with ha
  set a' := inclR (F := F) (AF F) (θ' : E) with ha'
  have hca : cA σ a = 1 - a := by
    rw [ha, hi, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hca' : cA σ a' = 1 - a' := by
    rw [ha', hi, eq_sub_of_add_eq' hθ', map_sub, map_one]
  set z := (a - a') * t with hz
  have hcz : cA σ z = z := by
    rw [hz, map_mul, map_sub, hca, hca', ht]; ring
  have h2 : Algebra.trace (AF F) (AE F E) z = 2 * Algebra.trace (AF F) (AE F E) (a * z) := by
    have e1 : Algebra.trace (AF F) (AE F E) (cA σ (a * z)) = Algebra.trace (AF F) (AE F E) (a * z) := htr _
    rw [map_mul, hca, hcz, sub_mul, one_mul, map_sub] at e1
    linear_combination e1
  have hmul : inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E) = a * (a - a') := by
    rw [ha, ha', ← map_sub, ← map_mul]; push_cast; rfl
  have key : symp (R := AF F) (cA σ) a (incM F X.J) (incM F W.J) γ γ =
      symp (R := AF F) (cA σ) a' (incM F X.J) (incM F W.J) γ γ +
        2 * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ := by
    simp only [symp, hmul]
    rw [← htdef, mul_assoc, ← hz, ← h2, hz, sub_mul, map_sub]; ring
  have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ hγ
  rw [key, mul_add, ← mul_assoc, invOf_mul_self, one_mul, AddChar.map_add_eq_mul, ← one_mul (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ), h1, mul_one]

end GlobalTheory.VacThetaInd
