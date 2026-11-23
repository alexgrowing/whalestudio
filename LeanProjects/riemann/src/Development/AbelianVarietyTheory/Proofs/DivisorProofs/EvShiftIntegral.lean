import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleHypothesisFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleSecondFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleThirdFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleFourthFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleFifthFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleTranslateSchwartzFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.ConeSoB

theorem ev_shift_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (L : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ),
    (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) →
    (∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (L φ)) →
    (∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = L φ) →
    ∀ ι ι₁, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∀ l : (AE F E)ˣ,
      ∃ (P : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F B.v₁)) (Q : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F B.v₁))
        (A : Matrix (Fin b) (Fin b) (Fv F B.v₁)) (A' : Matrix (Fin (a + b)) (Fin (a + b)) (Fv F B.v₁))
        (g : (Fin (a + (b + 2)) → Fv F B.v₁) → (Fin b → Fv F B.v₁) → ℂ) (x : Fv F B.v₁),
        ∀ Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁),
          ι₁ (L (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ)) Y =
            ∫ r, ∫ c, g r c * ι φ (P * insS (A * Y * A') r c x * Q) ∂(haarVec B.v₁ b) ∂(haarVec B.v₁ (a + (b + 2))) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis hinv ι ι₁ hι hι₁ φ hφ l
  have hψ : Continuous B.ψ := hT.base.std.1
  rw [(locOp_rho G.M'.co hψ B.v₁ (shiftB σ H H' l) hφ).2]
  obtain ⟨hPu0, hQu0⟩ := GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hPu : IsUnit (GlobalTheory.PlaneBasis.crdP B.τ₁ H).det := by
    exact Matrix.isUnit_nonsing_inv_det _ (by rwa [Matrix.det_transpose])
  have hQu : IsUnit (GlobalTheory.PlaneBasis.crdQ B.τ₁ H').det := by
    exact Matrix.isUnit_nonsing_inv_det _ hQu0
  set P := GlobalTheory.PlaneBasis.crdP B.τ₁ H with hP
  set Q := GlobalTheory.PlaneBasis.crdQ B.τ₁ H' with hQ
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ B.v₁) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ B.v₁
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ B.v₁ ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std B.v₁
  have hmaps : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      ι φ ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)) := fun φ h => hι.bij.mapsTo h
  let Λ : (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁) → ℂ) → ℂ := fun f =>
    ι₁ (L (Function.invFunOn ι (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) : Set _) f)) 0
  have hΛ : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), Λ (ι φ) = ι₁ (L φ) 0 := by
    intro φ hφ
    have hs := hι.bij.surjOn (hmaps φ hφ)
    have e : Function.invFunOn ι (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) : Set _) (ι φ) = φ :=
      hι.bij.injOn (Function.invFunOn_mem hs) hφ (Function.invFunOn_eq hs)
    change ι₁ (L (Function.invFunOn ι _ (ι φ))) 0 = _
    rw [e]
  have hadd : ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)),
      ∀ g ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)), Λ (f + g) = Λ f + Λ g := by
    intro f hf g hg
    obtain ⟨φf, hφf, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨φg, hφg, rfl⟩ := hι.bij.surjOn hg
    rw [← map_add, hΛ _ (add_mem hφf hφg), hΛ _ hφf, hΛ _ hφg, map_add, map_add]
    rfl
  have hsmul : ∀ z : ℂ, ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)), Λ (z • f) = z * Λ f := by
    intro z f hf
    obtain ⟨φf, hφf, rfl⟩ := hι.bij.surjOn hf
    rw [← map_smul, hΛ _ (Submodule.smul_mem _ z hφf), hΛ _ hφf, map_smul, map_smul]
    rfl
  have htr : ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)),
      ∀ (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁),
      Λ (fun Z => f (Z + P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 * Q)) = Λ f := by
    intro f hf r c
    obtain ⟨φf, hφf, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨φ', hφ', hL, hι'⟩ := GlobalTheory.T.seesaw_type_b_triple_second_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis hinv ι ι₁ hι hι₁ r c φf hφf
    have e : (fun Z => ι φf (Z + P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 * Q)) = ι φ' :=
      funext fun Z => (hι' Z).symm
    rw [e, hΛ _ hφ', hΛ _ hφf, hL]
  have hch : ∀ U : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁),
      (∀ (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁),
        ∑ i, ∑ j, U i j * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 i j = 0) →
      ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)),
      ∀ f₁ ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁)),
        (∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁),
          f₁ (P * Z * Q) = GlobalTheory.LatVac.psiAt B.ψ B.v₁ (∑ i, ∑ j, U i j * Z i j) * f (P * Z * Q)) → Λ f₁ = Λ f := by
    intro U hU f hf f₁ hf₁ hrel
    obtain ⟨φf, hφf, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨φ', hφ', h0, hι'⟩ := GlobalTheory.T.seesaw_type_b_triple_third_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis hinv ι ι₁ hι hι₁ U hU φf hφf
    have e : f₁ = ι φ' := by
      funext Z
      have hZ : P * (P⁻¹ * Z * Q⁻¹) * Q = Z := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.mul_one, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
      rw [← hZ, hι', hrel]
    rw [e, hΛ _ hφ', hΛ _ hφf, h0]
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.invertible_translate_schwartz_functional B.v₁ (GlobalTheory.LatVac.psiAt B.ψ B.v₁) hψc hψ1 P Q hPu hQu Λ hadd hsmul htr hch
  have hφs := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ B.v₁ (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (shiftB σ H H' l)) φ hφ
  obtain ⟨c₀, s, x, hS⟩ := GlobalTheory.T.seesaw_type_b_triple_fifth_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁ ι hι φ hφ l
  refine ⟨P, Q, 1, 1, fun r c => κ * c₀ * GlobalTheory.LatVac.psiAt B.ψ B.v₁ (s * r ⟨a, by omega⟩), x, fun Y => ?_⟩
  obtain ⟨φ', hφ', h0, hι'⟩ := GlobalTheory.T.seesaw_type_b_triple_fourth_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis hinv ι ι₁ hι hι₁ Y _ hφs
  rw [← h0, ← hΛ _ hφ', hκ _ (hmaps _ hφ'), Matrix.one_mul, Matrix.mul_one, ← integral_const_mul]
  congr 1
  funext r
  rw [← integral_const_mul]
  congr 1
  funext c
  have hins : insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 + insS Y 0 0 0 = insS Y r c 0 := by
    ext i j
    simp only [insS, Matrix.add_apply]
    split_ifs <;> simp
  rw [hι', ← Matrix.add_mul, ← Matrix.mul_add, hins, hS Y r c]
  ring

end GlobalTheory.ConeSoB

end
