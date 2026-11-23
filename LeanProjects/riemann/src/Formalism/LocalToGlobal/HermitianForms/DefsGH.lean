import Formalism.LocalToGlobal.HermitianForms.DefsSym

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

structure GLevH (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
    (lam : ∀ a v h, H a v h →* ℂˣ) where

  fr : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletion F)
  fr_lat : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) (x : Fin n → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ b, G.phi a v h (y b) = x b) ↔
      ∀ b, (((fr a v h)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  mem : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb,
    x ∈ S.Uloc v ↔ ∃ M ∈ H a v h, (M : Matrix (Fin n) (Fin n) (kv F v)) = redM F v (G.mat a v h (fr a v h) x)

  red : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), S.U → H a v h
  red_eq : ∀ a v h (x : S.U), (((red a v h x : H a v h) : GL (Fin n) (kv F v)) : Matrix (Fin n) (Fin n) (kv F v)) =
    redM F v (G.mat a v h (fr a v h) (bc (prV (E := E) v) x.1))

  chi_eq : ∀ x : S.U, (S.chi x : ℂ) = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal),
    (((lam a v h (red a v h x) : ℂˣ) : ℂ))⁻¹

  chi_unit : ∀ x : S.U, ‖(S.chi x : ℂ)‖ = 1

def GLev.toH {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl)
    (H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
    (lam : ∀ i v h, H i v h →* ℂˣ)
    (hH : ∀ i v h (M : GL (Fin n) (kv F v)), M ∈ H i v h ↔ InJ a t fc zl (M : Matrix (Fin n) (Fin n) (kv F v)))
    (hlam : ∀ i v h (M : H i v h), ((lam i v h M : ℂˣ) : ℂ) =
      lamJ (G.psi0 i v h) (G.chiB i v h) a t nb skip ((M : GL (Fin n) (kv F v)) : Matrix (Fin n) (Fin n) (kv F v)))
    (hunit : ∀ i v (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb, IsUnit (redM F v (G.mat i v h (L.fr i v h) x))) :
    GLevH S G H lam where
  fr := L.fr
  fr_lat := L.fr_lat
  mem i v h x hx := by
    rw [L.mem i v h x hx]
    constructor
    · intro hJ; exact ⟨(hunit i v h x hx).unit, (hH i v h _).2 hJ, rfl⟩
    · rintro ⟨M, hM, e⟩; rw [← e]; exact (hH i v h M).1 hM
  red i v h x :=
    ⟨(hunit i v h _ (S.Uloc_lev v (((S.U_eq x.1).1 x.2).2 v))).unit,
      (hH i v h _).2 ((L.mem i v h _ (S.Uloc_lev v (((S.U_eq x.1).1 x.2).2 v))).1 (((S.U_eq x.1).1 x.2).2 v))⟩
  red_eq i v h x := rfl
  chi_eq x := by
    rw [L.chi_eq x]
    congr 1; funext i; congr 1; funext v; congr 1; funext h
    rw [hlam]; rfl
  chi_unit := L.chi_unit

end Loc

end Formalism.L2.Forms
