import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Formalism.L2.Host UpperTheory.V.TR
open GlobalTheory.CuspRep (GA Af invT locGL)
open scoped ContDiff

namespace UpperTheory.V.Af.Gk

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem conj_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun x => starRingEnd ℂ (φ x)) ∈ Sm E a := fun g => by
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

variable (E a) in

def conjFn : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun φ := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem_Sm φ.2⟩
  invFun φ := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem_Sm φ.2⟩
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (starRingEnd ℂ) _ _
  map_smul' _ _ := Subtype.ext <| funext fun _ => map_mul (starRingEnd ℂ) _ _
  left_inv _ := Subtype.ext <| funext fun _ => Complex.conj_conj _
  right_inv _ := Subtype.ext <| funext fun _ => Complex.conj_conj _

@[simp] theorem conjFn_apply (φ : Sm E a) (g : GA E a) : (conjFn E a φ).1 g = starRingEnd ℂ (φ.1 g) := rfl

@[simp] theorem conjFn_conjFn (φ : Sm E a) : conjFn E a (conjFn E a φ) = φ := (conjFn E a).left_inv φ

theorem act_conjFn (o : Op E a) (φ : Sm E a) : act o (conjFn E a φ) = conjFn E a (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    refine Subtype.ext <| funext fun g => ?_
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) _ X = starRingEnd ℂ (fderiv ℝ (chart φ.1 g) _ X)
    rw [chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

structure IsHerm (π : TR.CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) : Prop where
  definite : ∀ φ, H φ φ = 0 → φ = 0
  fin : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ
  cpt : ∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ
  lie : ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0

def HasPairing (π : TR.CuspSub E a) : Prop :=
  ∃ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af E) k)) ψ) = B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0

def ConjCusp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : Sm F a),
    TR.IsCuspForm φ → TR.IsCuspForm (conjFn F a φ)

def ConjSub : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∃ (π' : TR.CuspSub F a) (C : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, C (π.op o φ) = π'.op o (C φ)

def HeckeAdj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    (∀ g x y, H (ρ g x) (ρ g y) = H x y) → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w a), ∀ ϖ, Formalism.UG.IsUnifV F w ϖ → ∀ j : ℕ,
      H (GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov F w) ϖ j) x) x =
        H x (GlobalTheory.LFun.heckeVec (ρ.comp (invT a (w.adicCompletion F))) (GlobalTheory.LFun.KGL w a) (Formalism.UG.Tj ℂ a (Formalism.UG.Ov F w) ϖ j) x)

def SatConj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V)
    (ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion F)) W) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (C : V ≃ₗ⋆[ℂ] W),
    (∀ x, H x x = 0 → x = 0) → (∀ g x y, H (ρ g x) (ρ g y) = H x y) → (∀ g x, C (ρ g x) = ρ' g (C x)) →
    ∀ B, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map (·⁻¹))

def SatAE : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B

def OneScalar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∃ s : ℂ, ∀ φ ∈ π.V, TR.lie F a (oneL F a) φ = s • φ

def ExpoChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℂ), ∃ χ : HChar F, ∀ v, TR.expo χ v = s

def UnitTwist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ π : TR.CuspSub F a,
    ∃ χ : HChar F, ∀ φ ∈ (π.twist χ).V, TR.lie F a (oneL F a) φ = 0

def PairOfTwist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a) (χ : HChar F),
    HasPairing (π.twist χ) → HasPairing π

def PairZero : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 0), HasPairing π

def HermEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ π : TR.CuspSub F a,
    (∀ φ ∈ π.V, TR.lie F a (oneL F a) φ = 0) → ∃ H, IsHerm π H

theorem hasPairing_of_herm {π : TR.CuspSub E a} {H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ} (hH : IsHerm π H)
    (D : π.dual.V ≃ₗ⋆[ℂ] π.V) (hD : ∀ o φ, D (π.dual.op o φ) = π.op o (D φ)) : HasPairing π := by
  let S : π.V ≃ₗ⋆[ℂ] π.V := π.toDual.trans D
  have hS : ∀ o φ, S (π.op o φ) = π.op (invTOp o) (S φ) := fun o φ => by
    change D (π.toDual _) = π.op _ (D (π.toDual φ))
    rw [← hD, CuspSub.op_toDual, invTOp_invTOp]
  refine ⟨H ∘ₛₗ S.toLinearMap, fun φ h => S.injective ((hH.definite _ (h (S φ))).trans (map_zero S).symm),
    fun ψ h => hH.definite _ ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · simpa using h (S.symm ψ)
  · change H (S _) _ = H (S φ) ψ
    rw [hS]
    exact hH.fin _ _ _
  · change H (S _) _ = H (S φ) ψ
    rw [hS]
    exact hH.cpt _ _ _
  · change H (S _) _ + H (S φ) _ = 0
    rw [hS]
    exact hH.lie _ _ _

theorem gelfandKazhdan_of (h1 : ConjSub) (h2 : SatConj) (h3 : SatAE) (h4 : UnitTwist) (h5 : PairOfTwist) (h6 : PairZero)
    (h7 : HermEx) (smo : Published.StrongMultOneReal) : Published.GelfandKazhdanReal := by
  intro F _ _ _ a π
  change HasPairing π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact h6 F π
  obtain ⟨χ, hχ⟩ := h4 F a ha π
  refine h5 F a π χ ?_
  generalize π.twist χ = π at hχ
  obtain ⟨H, hH⟩ := h7 F a ha π hχ
  obtain ⟨π', C, hC⟩ := h1 F a π
  obtain ⟨T, hT⟩ := smo F a ha π.dual π' ((h3 F a π).mono fun w ⟨B, hB⟩ => ⟨_, hB.dual,
    h2 F a w _ _ (π.locRep w) (π'.locRep w) H C hH.definite (fun g => hH.fin (locGL F a w g))
      (fun g => hC (.fin (locGL F a w g))) B hB⟩)
  refine hasPairing_of_herm hH (T.trans C.symm) fun o φ => C.injective ?_
  change C (C.symm (T _)) = C (π.op o (C.symm (T φ)))
  rw [hC, C.apply_symm_apply, C.apply_symm_apply, hT]

end UpperTheory.V.Af.Gk
