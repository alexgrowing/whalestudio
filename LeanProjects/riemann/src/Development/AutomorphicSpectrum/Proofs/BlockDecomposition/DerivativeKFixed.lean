import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.TemperedDerivatives.StepsD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzStable

noncomputable section

open MeasureTheory Matrix Ad3.K Ad3.K.LC

namespace GlobalTheory.CompanionTheory.GodementKFinC

open GlobalTheory.CompanionTheory.GodementSectionC

def mnr (a b : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ := p.1 0 a * p.1 1 b - p.1 0 b * p.1 1 a

def qcj (c : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (starRingEnd ℂ) (p.2 0 * p.1 0 c + p.2 1 * p.1 1 c)

def gs (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * ((∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ))

def spM : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) :=
  Submodule.span ℂ {mnr 0 1, mnr 0 2, mnr 1 2}

def spQ : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) :=
  Submodule.span ℂ {qcj 0, qcj 1, qcj 2}

def spG : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) := Submodule.span ℂ {gs}

def spP (a b : ℕ) : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) := spM ^ a * spQ ^ b * spG

theorem spP_fg (a b : ℕ) : (spP a b).FG := by
  have h1 : spM.FG := Submodule.fg_span (by simp)
  have h2 : spQ.FG := Submodule.fg_span (by simp)
  have h3 : spG.FG := Submodule.fg_span (by simp)
  exact ((h1.pow a).mul (h2.pow b)).mul h3

instance spP_finiteDimensional (a b : ℕ) : FiniteDimensional ℂ (spP a b) :=
  Module.Finite.iff_fg.2 (spP_fg a b)

theorem norm_det_eq_one (o : Matrix (Fin 3) (Fin 3) ℂ) (ho : o * oᴴ = 1) : ‖o.det‖ = 1 := by
  have h : o.det * (starRingEnd ℂ) o.det = 1 := by
    have := congrArg Matrix.det ho
    rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  rw [Complex.mul_conj'] at h
  have h' : ‖o.det‖ ^ 2 = 1 := by exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'

theorem sqs_mul (o : Matrix (Fin 3) (Fin 3) ℂ) (ho : o * oᴴ = 1) (X : M23) (r : Fin 2) :
    ∑ c, ‖(Matrix.of X * o) r c‖ ^ 2 = ∑ c, ‖X r c‖ ^ 2 := by
  have h : (X r ᵥ* o) ⬝ᵥ star (X r ᵥ* o) = X r ⬝ᵥ star (X r) := by
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ho, Matrix.vecMul_one]
  have hn : ∀ v : Fin 3 → ℂ, v ⬝ᵥ star v = ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  rw [hn, hn] at h
  exact_mod_cast h

theorem sec_translate (k : ℕ) (Ψ Ψ₀ : Sw) (g o : GL (Fin 3) ℂ)
    (ho : ‖(o : Matrix (Fin 3) (Fin 3) ℂ).det‖ = 1)
    (hΨ : ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ₀ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (o : Matrix (Fin 3) (Fin 3) ℂ)), q)) :
    sec k Ψ (g * o) = sec k Ψ₀ g := by
  unfold sec
  simp only [inn_mul_right Ψ Ψ₀ g o hΨ]
  rw [Units.val_mul, Matrix.det_mul, norm_mul, ho, mul_one]

theorem gauK_translate_mem (k : ℕ) (o : Matrix (Fin 3) (Fin 3) ℂ) (ho : o * oᴴ = 1) :
    (fun p : M23 × (Fin 2 → ℂ) => gauK k (Matrix.of.symm (Matrix.of p.1 * o), p.2)) ∈
      spP (2 * k - 2) (4 * k - 4) := by
  set u : M23 × (Fin 2 → ℂ) → ℂ :=
    (o 0 0 * o 1 1 - o 0 1 * o 1 0) • mnr 0 1 + (o 0 0 * o 2 1 - o 0 1 * o 2 0) • mnr 0 2 +
      (o 1 0 * o 2 1 - o 1 1 * o 2 0) • mnr 1 2 with hu
  set v : M23 × (Fin 2 → ℂ) → ℂ :=
    (starRingEnd ℂ) (o 0 0) • qcj 0 + (starRingEnd ℂ) (o 1 0) • qcj 1 +
      (starRingEnd ℂ) (o 2 0) • qcj 2 with hv
  have hum : u ∈ spM := by
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hvm : v ∈ spQ := by
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have heq : (fun p : M23 × (Fin 2 → ℂ) => gauK k (Matrix.of.symm (Matrix.of p.1 * o), p.2)) =
      u ^ (2 * k - 2) * v ^ (4 * k - 4) * gs := by
    funext p
    have hs : (∑ r, ∑ c, ‖(Matrix.of p.1 * o) r c‖ ^ 2) = ∑ r, ∑ c, ‖p.1 r c‖ ^ 2 :=
      Finset.sum_congr rfl fun r _ => sqs_mul o ho p.1 r
    have h1 : (Matrix.of p.1 * o) 0 0 * (Matrix.of p.1 * o) 1 1 -
        (Matrix.of p.1 * o) 0 1 * (Matrix.of p.1 * o) 1 0 = u p := by
      simp only [hu, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mnr]
      ring
    have h2 : (starRingEnd ℂ) (p.2 0 * (Matrix.of p.1 * o) 0 0 + p.2 1 * (Matrix.of p.1 * o) 1 0) =
        v p := by
      simp only [hv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, qcj, map_add, map_mul]
      ring
    simp only [gauK, Pi.mul_apply, Pi.pow_apply, gs]
    change ((Matrix.of p.1 * o) 0 0 * (Matrix.of p.1 * o) 1 1 -
        (Matrix.of p.1 * o) 0 1 * (Matrix.of p.1 * o) 1 0) ^ (2 * k - 2) *
      (starRingEnd ℂ) (p.2 0 * (Matrix.of p.1 * o) 0 0 + p.2 1 * (Matrix.of p.1 * o) 1 0) ^ (4 * k - 4) *
      Complex.exp (-(2 * Real.pi : ℂ) *
        ((∑ r, ∑ c, ‖(Matrix.of p.1 * o) r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ)) = _
    rw [h1, h2, hs]
  rw [heq]
  exact Submodule.mul_mem_mul (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hum _)
    (Submodule.pow_mem_pow _ hvm _)) (Submodule.subset_span rfl)

theorem translates_finiteDimensional : DKfd := by
  intro hS k hk Ψ hΨ
  let L : Sw →ₗ[ℂ] (GL (Fin 3) ℂ → ℂ) :=
    { toFun := sec k
      map_add' := fun A B => (hS k hk A B 0).1
      map_smul' := fun c A => (hS k hk A 0 c).2 }
  let co : Sw →ₗ[ℂ] (M23 × (Fin 2 → ℂ) → ℂ) :=
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := fun A B h => SchwartzMap.ext (congrFun h)
  let F : Submodule ℂ Sw := (spP (2 * k - 2) (4 * k - 4)).comap co
  let e : F →ₗ[ℂ] spP (2 * k - 2) (4 * k - 4) := co.restrict (fun _ hx => hx)
  have he : Function.Injective e := fun A B h =>
    Subtype.ext (hco (congrArg Subtype.val h))
  haveI : FiniteDimensional ℂ F := FiniteDimensional.of_injective e he
  have hle : Submodule.span ℂ {W' | ∃ o ∈ U3, W' = fun g => sec k Ψ (g * o)} ≤ F.map L := by
    refine Submodule.span_le.2 ?_
    rintro W ⟨o, ho, rfl⟩
    obtain ⟨Ψ₀, hΨ₀⟩ := exists_rightTranslate o Ψ
    refine ⟨Ψ₀, ?_, funext fun g => ?_⟩
    · have hf : co Ψ₀ = fun p : M23 × (Fin 2 → ℂ) =>
          gauK k (Matrix.of.symm (Matrix.of p.1 * (o : Matrix (Fin 3) (Fin 3) ℂ)), p.2) := by
        funext p
        change Ψ₀ (p.1, p.2) = _
        rw [hΨ₀, hΨ]
      change co Ψ₀ ∈ spP (2 * k - 2) (4 * k - 4)
      rw [hf]
      exact gauK_translate_mem k _ ho
    · exact (sec_translate k Ψ Ψ₀ g o (norm_det_eq_one _ ho) hΨ₀).symm
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.GodementKFinC
