import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInfStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PureStabFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (c : AF F) (g₁ g : UA σ J)
    (hg : c • (mat g - 1) = 0) (hg₁ : c • (mat g₁ - 1) = 0) : c • (mat (g₁⁻¹ * g) - 1) = 0 := by
  have hmul : mat (g₁⁻¹ * g) = mat g₁⁻¹ * mat g := rfl
  have hNM : mat g₁⁻¹ * mat g₁ = 1 := by
    change ((g₁.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * (g₁.1 : Matrix _ _ _) = 1
    exact Units.inv_mul g₁.1
  have key : mat (g₁⁻¹ * g) - 1 = mat g₁⁻¹ * (mat g - 1) - mat g₁⁻¹ * (mat g₁ - 1) := by
    rw [hmul, Matrix.mul_sub, Matrix.mul_sub, hNM, Matrix.mul_one]; abel
  rw [key, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hg, hg₁, Matrix.mul_zero, sub_zero]

open Classical in

theorem supp_of_split {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (w : Pl F) (S : Finset (Pl F))
    (g₁ g₂ : UA σ J) (hg : ∀ u : AF F, (∀ x ∈ insert w S, evFin F x u = 0) → u • (mat (g₁ * g₂) - 1) = 0)
    (hg₁ : At (evFin F w) (mat g₁ - 1)) (hg₂ : ∀ u : AF F, At (evFin F w) u → u • (mat g₂ - 1) = 0) :
    ∀ u : AF F, (∀ x ∈ S, evFin F x u = 0) → u • (mat g₂ - 1) = 0 := by
  intro u hu
  set e : AF F := GlobalTheory.UnitaryPlaceSplit.idemAt w with he
  have hew : evFin F w e = 1 := GlobalTheory.UnitaryPlaceSplit.evFin_idemAt w
  have h1 : At (evFin F w) (u * e) := fun u' hu' => by
    change u' * (u * e) = 0
    rw [← mul_assoc]
    exact GlobalTheory.UnitaryPlaceSplit.mul_idemAt_of_evFin w (by rw [map_mul, hu', zero_mul])
  have hcw : evFin F w (u * (1 - e)) = 0 := by rw [map_mul, map_sub, map_one, hew, sub_self, mul_zero]
  have h2 : (u * (1 - e)) • (mat g₂ - 1) = 0 := by
    have e2 : g₂ = g₁⁻¹ * (g₁ * g₂) := (inv_mul_cancel_left g₁ g₂).symm
    rw [e2]
    refine smul_mat_inv_mul _ _ _ (hg _ fun x hx => ?_) (hg₁ _ hcw)
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hcw
    · rw [map_mul, hu x hx, zero_mul]
  have hsplit : u = u * e + u * (1 - e) := by ring
  rw [hsplit, add_smul, hg₂ _ h1, h2, add_zero]

theorem pure_stab_fin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro g h hg hh f φ hφ hcof
    have hg1 : g = 1 := by
      have := hg 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    have hh1 : h = 1 := by
      have := hh 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    subst hg1 hh1
    refine ⟨φ, hφ, fun _ _ => rfl, ?_⟩
    rw [Prod.mk_one_one, map_one]
    rfl
  | insert w S hw ih =>
    intro g h hg hh f φ hφ hcof
    obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ a' G.V'.J w g
    obtain ⟨h₁, h₂, rfl, hh₁, hh₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ (a + a') G.W.J w h
    have hg₂S := supp_of_split w S g₁ g₂ hg hg₁ hg₂
    have hh₂S := supp_of_split w S h₁ h₂ hh hh₁ hh₂
    obtain ⟨φ₂, hφ₂, hφ₂S, hφ₂e⟩ := ih g₂ h₂ hg₂S hh₂S f φ hφ hcof
    have hcof₂ : ∀ᶠ x in Filter.cofinite, φ₂ x = G.M'.vac x := by
      filter_upwards [hcof, S.eventually_cofinite_notMem] with x hx hxS
      rw [hφ₂S x hxS, hx]
    obtain ⟨φ', hφ', hφ'w, -, hφ'e⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT w g₁ hg₁ h₁ hh₁ f φ₂ hφ₂ hcof₂
    refine ⟨φ', hφ', fun x hx => ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at hx
      rw [hφ'w x hx.1, hφ₂S x hx.2]
    · have hpr : ((g₁ * g₂, h₁ * h₂) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) := rfl
      rw [hpr, map_mul, Module.End.mul_apply, hφ₂e, hφ'e]

end GlobalTheory.PureStabFin
