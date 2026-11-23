import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.WhSymProof

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem wh_eq_of_equiv (f : GL ι K ≃ GL κ K) (Φ : ι → ι → Prop) (Φ' : κ → κ → Prop) (E : ι → ι → K)
    (E' : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL ι K → ℂ) (χ' : GL κ K → ℂ)
    (hm : ∀ x, f x ∈ patSet K Φ' ↔ x ∈ patSet K Φ)
    (hc : ∀ x, patChar E' ψ₀ (f x) = patChar E ψ₀ x)
    (hχ : ∀ x, χ' (f x) = χ x) :
    wh Φ E ψ₀ χ = wh Φ' E' ψ₀ χ' := by
  classical
  have himg : patSet K Φ' = f '' patSet K Φ := by
    ext y
    constructor
    · intro hy
      exact ⟨f.symm y, (hm _).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).2 hx
  unfold wh
  rw [himg, Set.ncard_image_of_injective _ f.injective, ← himg]
  congr 1
  refine Fintype.sum_equiv f _ _ fun x => ?_
  by_cases hx : x ∈ patSet K Φ
  · rw [if_pos hx, if_pos ((hm x).2 hx), hc, hχ]
  · rw [if_neg hx, if_neg (fun h => hx ((hm x).1 h))]

theorem glEquiv_entry (e : ι ≃ κ) (x : GL ι K) (i j : ι) :
    ((glEquiv K e x : GL κ K) : Matrix κ κ K) (e i) (e j) = (x : Matrix ι ι K) i j := by
  rw [Formalism.L2.PT.coe_glEquiv]
  simp

theorem glEquiv_mem_patSet (Φ : κ → κ → Prop) (e : ι ≃ κ) (x : GL ι K) :
    glEquiv K e x ∈ patSet K Φ ↔ x ∈ patSet K (fun i j => Φ (e i) (e j)) := by
  constructor
  · intro h i j
    have h' := h (e i) (e j)
    rw [glEquiv_entry] at h'
    exact ⟨fun hij => h'.1 (congrArg e hij), fun hij => h'.2 (fun h2 => hij (e.injective h2))⟩
  · intro h i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    have h' := h i j
    rw [glEquiv_entry]
    exact ⟨fun hij => h'.1 (e.injective hij), fun hij => h'.2 (fun h2 => hij (congrArg e h2))⟩

theorem patChar_glEquiv (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (e : ι ≃ κ) (x : GL ι K) :
    patChar E ψ₀ (glEquiv K e x) = patChar (fun i j => E (e i) (e j)) ψ₀ x := by
  unfold patChar
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [glEquiv_entry]

theorem wh_renumber (Φ : κ → κ → Prop) (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ) (e : ι ≃ κ) :
    wh (fun i j => Φ (e i) (e j)) (fun i j => E (e i) (e j)) ψ₀ (fun x => χ (glEquiv K e x)) =
      wh Φ E ψ₀ χ :=
  wh_eq_of_equiv (glEquiv K e).toEquiv _ _ _ _ ψ₀ _ _ (fun x => glEquiv_mem_patSet Φ e x)
    (fun x => patChar_glEquiv E ψ₀ e x) (fun _ => rfl)

theorem glEquiv_trans_perm (e e' : ι ≃ κ) (x : GL ι K) :
    glEquiv K e' x = glEquiv K (e.symm.trans e') (glEquiv K e x) := by
  apply Units.ext
  ext a b
  obtain ⟨i, rfl⟩ := e'.surjective a
  obtain ⟨j, rfl⟩ := e'.surjective b
  have hs : ∀ i, (e.symm.trans e') (e i) = e' i := fun i => by simp
  rw [glEquiv_entry e' x i j, ← hs i, ← hs j, glEquiv_entry, glEquiv_entry]

theorem class_renumber (χ : GL κ K → ℂ) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (e e' : ι ≃ κ) (x : GL ι K) :
    χ (glEquiv K e x) = χ (glEquiv K e' x) := by
  rw [glEquiv_trans_perm e e' x, GlobalTheory.SerOSys.TranspLabel.glEquiv_perm, hχ]

def diagGL (t : κ → Kˣ) : GL κ K :=
  ⟨Matrix.diagonal fun i => (t i : K), Matrix.diagonal fun i => (((t i)⁻¹ : Kˣ) : K),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

omit [Fintype K] [DecidableEq K] in

theorem diagGL_conj_entry (t : κ → Kˣ) (u : GL κ K) (i j : κ) :
    ((diagGL t * u * (diagGL t)⁻¹ : GL κ K) : Matrix κ κ K) i j =
      (t i : K) * (u : Matrix κ κ K) i j * ((t j)⁻¹ : Kˣ) := by
  have hinv : (((diagGL t)⁻¹ : GL κ K) : Matrix κ κ K) = Matrix.diagonal fun i => (((t i)⁻¹ : Kˣ) : K) := rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  show ((Matrix.diagonal (fun i => (t i : K)) * (u : Matrix κ κ K)) *
    Matrix.diagonal (fun i => (((t i)⁻¹ : Kˣ) : K)) : Matrix κ κ K) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem wh_torus (Φ : κ → κ → Prop) (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (t : κ → Kˣ) :
    wh Φ (fun i j => (t i : K) * E i j * ((t j)⁻¹ : Kˣ)) ψ₀ χ = wh Φ E ψ₀ χ := by
  refine wh_eq_of_equiv (MulAut.conj (diagGL t)).toEquiv _ _ _ _ ψ₀ _ _ (fun x => ?_) (fun x => ?_)
    (fun x => ?_)
  · show diagGL t * x * (diagGL t)⁻¹ ∈ patSet K Φ ↔ x ∈ patSet K Φ
    constructor
    · intro h i j
      have h' := h i j
      rw [diagGL_conj_entry] at h'
      refine ⟨fun hij => ?_, fun hij hn => ?_⟩
      · subst hij
        have h1 := h'.1 rfl
        have h2 : (t i : K) ≠ 0 := (t i).ne_zero
        have h3 : (((t i)⁻¹ : Kˣ) : K) = (t i : K)⁻¹ := by simp
        rw [h3] at h1
        field_simp at h1
        exact h1
      · have h1 := h'.2 hij hn
        simpa using h1
    · intro h i j
      have h' := h i j
      rw [diagGL_conj_entry]
      refine ⟨fun hij => ?_, fun hij hn => ?_⟩
      · subst hij
        rw [h'.1 rfl]
        simp
      · rw [h'.2 hij hn]
        simp
  · show patChar E ψ₀ (diagGL t * x * (diagGL t)⁻¹) = patChar _ ψ₀ x
    unfold patChar
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [diagGL_conj_entry]
    ring
  · show χ (diagGL t * x * (diagGL t)⁻¹) = χ x
    exact hχ _ _

theorem whSym : ReciprocityTheory.Ty.Fin.St.WhSym := by
  intro K _ _ _ ι κ _ _ _ _ Φ E ψ₀ χ
  exact ⟨fun e => wh_renumber Φ E ψ₀ χ e, fun hχ =>
    ⟨fun e e' x => class_renumber χ hχ e e' x, fun t => wh_torus Φ E ψ₀ χ hχ t⟩⟩

end GlobalTheory.CompanionTheory.TyFin.WhSymProof
