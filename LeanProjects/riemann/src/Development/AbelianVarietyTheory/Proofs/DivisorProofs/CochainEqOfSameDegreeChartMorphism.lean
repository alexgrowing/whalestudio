import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem cochain_fromTriv_eq (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    {k : K.K} (T : K.Obj) (hle : K.le l T.k k) (ρ : Hol (K.W k) →+* T.C)
    (hρ : Close T.J (T.ρ.comp (sh hle)) ρ) :
    ∀ hc : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) T.C f,
      h _ _ (fromTriv T hle ρ hc hρ) = h _ _ (ptHom T hle) := by
  induction hρ with
  | refl => intro hc; rfl
  | @tail ρ₁ ρ₂ hab s ih =>
    intro hc₂
    obtain ⟨n, h1, h2, h3⟩ := s
    have hc₁ : ∀ f, ρ₁ (K.cst k f) = algebraMap (Hol F.V) T.C f := fun f ↦ by
      rw [← hc₂ f, h3]
      simp [dw_cst]
    rw [← ih hc₁]
    obtain ⟨χ, hdeg, e0, e1, -⟩ := GlobalTheory.AnPer.Charts.exists_jet_factor K (fromTriv T hle ρ₁ hc₁ hab)
      (fromTriv T hle ρ₂ hc₂ (Relation.ReflTransGen.tail hab ⟨n, h1, h2, h3⟩)) n rfl h1 h2 (fun x ↦ h3 x)
    rw [← e0, ← e1]
    exact (H k T χ hdeg).symm

theorem cochain_eq_ptHom {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T) (hf : f.deg = l) :
    h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  subst hf
  letI := (K.triv k).alg
  exact cochain_fromTriv_eq K h f.deg H T (Charts.Hom.le f) f.φ.toRingHom (Charts.Hom.close f)
    (fun x ↦ f.φ.commutes x)

end GlobalTheory.AnPer.Charts
