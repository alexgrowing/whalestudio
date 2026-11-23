import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertRhoLaw

theorem darboux_rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w w' : W) (Φ : (κ → R) → ℂ) :
    d.rho ψ w (d.rho ψ w' Φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2

theorem darboux_rho_zero {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (Φ : (κ → R) → ℂ) :
    d.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem eq_of_tens_eq {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r 0 ≠ 0) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : r (0 + z) = r 0 := hr 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.InertRhoLaw

namespace GlobalTheory.InertRhoLaw

theorem rho_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hEq, -, -, -, -, -⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hA : ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)),
      G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R) =
        tens (evFin F v) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R :=
    fun x m => hρ x m R (hR _ m.2)
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (Submodule.zero_mem _)).1
  refine ⟨?_, fun x y => ?_⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    rw [← hA 0 m, map_zero, darboux_rho_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    have e1 := hA x (ρ y m)
    have e2 := hA y m
    have e3 := hA (x + y) m
    have hl := darboux_rho_rho G.M'.co B.ψ (κ x) (κ y) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)
    rw [e2, e1, ← map_add, e3, ← hEq x y] at hl
    rw [Module.End.mul_apply, hl, LinearMap.smul_apply, Submodule.coe_smul]
    funext z
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.InertRhoLaw

end
