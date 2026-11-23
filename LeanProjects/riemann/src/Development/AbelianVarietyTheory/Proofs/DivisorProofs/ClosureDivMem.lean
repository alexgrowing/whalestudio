import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUSuppSub

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R)

theorem fix_mul {A B : Matrix n n R} (hA : c • (A - 1) = A - 1) (hB : c • (B - 1) = B - 1) :
    c • (A * B - 1) = A * B - 1 := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hA, hB]

theorem fix_inv {A A' : Matrix n n R} (h : A' * A = 1) (hA : c • (A - 1) = A - 1) :
    c • (A' - 1) = A' - 1 := by
  have e : A' - 1 = -(A' * (A - 1)) := by rw [Matrix.mul_sub, h, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hA]

theorem fix_conj {A K K' : Matrix n n R} (h : K * K' = 1) (hA : c • (A - 1) = A - 1) :
    c • (K * A * K' - 1) = K * A * K' - 1 := by
  have e : K * A * K' - 1 = K * (A - 1) * K' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hA]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

abbrev mv (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mv_mul (g h : HA (AF F) σ J) : mv σ J (g * h) = mv σ J g * mv σ J h := rfl

theorem mv_one : mv σ J 1 = 1 := rfl

theorem mv_inv_mul (g : HA (AF F) σ J) : mv σ J g⁻¹ * mv σ J g = 1 := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mul_inv (g : HA (AF F) σ J) : mv σ J g * mv σ J g⁻¹ = 1 := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

theorem mem_SUSupp_iff {ε : AF F} {g : HA (AF F) σ J} : g ∈ SUSupp σ J ε ↔ g ∈ SUAdelic σ J ∧
    algebraMap (AF F) (AF F ⊗[F] E) ε • (mv σ J g - 1) = mv σ J g - 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext i j
    simpa using h2 i j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    simpa using this

theorem closure_div_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, ∀ y ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, x * y⁻¹ ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ _ M J _ S₁ S₂ ε _
  set c := algebraMap (AF F) (AF F ⊗[F] E) ε with hc
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hconj : ∀ k g : HA (AF F) σ J, g ∈ SUAdelic σ J → k * g * k⁻¹ ∈ SUAdelic σ J := by
    intro k g hg
    rw [StrongApprox.mem_SUAdelic] at hg ⊢
    change (mv σ J g).det = 1 at hg
    change (mv σ J (k * g * k⁻¹)).det = 1
    rw [mv_mul, mv_mul, Matrix.det_mul, Matrix.det_mul, hg, mul_one, ← Matrix.det_mul, mv_mul_inv,
      Matrix.det_one]
  have hdiv : ∀ x ∈ S, ∀ y ∈ S, x * y⁻¹ ∈ S := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩ _ ⟨γ', hγ', h', hh', rfl⟩
    refine ⟨γ * γ'⁻¹, (SURat σ J).mul_mem hγ ((SURat σ J).inv_mem hγ'), γ' * (h * h'⁻¹) * γ'⁻¹, ?_, by group⟩
    rw [mem_SUSupp_iff] at hh hh' ⊢
    refine ⟨hconj γ' _ ((SUAdelic σ J).mul_mem hh.1 ((SUAdelic σ J).inv_mem hh'.1)), ?_⟩
    rw [mv_mul, mv_mul, mv_mul]
    exact fix_conj _ (mv_mul_inv σ J γ') (fix_mul _ hh.2 (fix_inv _ (mv_inv_mul σ J h') hh'.2))
  have hne : S.Nonempty := ⟨1, 1, (SURat σ J).one_mem, 1,
    (mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [mv_one, sub_self, smul_zero]⟩, by simp⟩
  let P : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv S hne hdiv
  have hP : (P.topologicalClosure : Set (HA (AF F) σ J)) = closure S := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  intro x hx y hy
  rw [← hP] at hx hy ⊢
  exact P.topologicalClosure.mul_mem hx (P.topologicalClosure.inv_mem hy)

end GlobalTheory.SUSuppSub

end
