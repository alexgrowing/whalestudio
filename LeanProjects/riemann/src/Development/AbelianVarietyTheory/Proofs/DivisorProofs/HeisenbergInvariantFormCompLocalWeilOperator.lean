import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacEquiv

theorem acts_schr_of_ref {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (AF F) ℂ)
    (w : (κ → AF F) × (κ → AF F)) (h₁ : At (evFin F v) w.1) (h₂ : At (evFin F v) w.2)
    (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x)
    (φ φ₁ : (κ → Fv F v) → ℂ) (h : schr ψ w (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R) :
    Acts (evFin F v) (schr ψ w) φ φ₁ := by
  intro r hr
  funext x
  set y : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (x i)) with hyD
  have hev : ∀ i, evFin F v (y i) = evFin F v (x i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have hy : At (evFin F v) y := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hRy : R y = R 0 := by simpa using hR 0 y hy
  have hRyw : R (y + w.1) = R y := hR y w.1 h₁
  have hrx : r (x + w.1) = r x := hr.1 x w.1 h₁
  have hdot : x ⬝ᵥ w.2 = y ⬝ᵥ w.2 := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : evFin F v (x i - y i) = 0 := by rw [map_sub, hev, sub_self]
    have h0 := congrFun (h₂ (x i - y i) hz) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← sub_eq_zero, ← sub_mul, h0]
  have hφ : (fun i => evFin F v ((x + w.1) i)) = (fun i => evFin F v ((y + w.1) i)) := by
    funext i
    simp only [Pi.add_apply, map_add, hev]
  have hφ₁ : (fun i => evFin F v (x i)) = (fun i => evFin F v (y i)) := by
    funext i
    exact (hev i).symm
  have key := congrFun h y
  simp only [schr, tens] at key ⊢
  rw [hRyw, hRy] at key
  rw [hdot, hrx, hφ₁]
  have hcanc : ψ (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * φ (fun i => evFin F v ((x + w.1) i)) =
      φ₁ (fun i => evFin F v (y i)) := by
    apply mul_right_cancel₀ hR0
    rw [hφ, ← key, mul_assoc]
  rw [← mul_assoc, hcanc]

theorem heisInv_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v m C l hl g _ S hS u hu φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hRest⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hsp := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  set u' := GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u with hu'D
  have hu'eq : u' = mat g * u := by
    simp [hu'D, GlobalTheory.WeilM.actAB, mat]
  obtain ⟨huAt, z, hz⟩ := hu
  have hAt' : At (evFin F v) u' := by
    intro c hc
    rw [hu'eq, ← Matrix.mul_smul, huAt c hc, Matrix.mul_zero]
  have hlag : u' ∈ GlobalTheory.InertVacLag.lagAt v C := ⟨hAt', mat g * z, by rw [hu'eq, hz, Matrix.mul_assoc]⟩
  have hco1 : At (evFin F v) (G.M'.co.e u').1 := by
    intro c hc
    rw [← Prod.smul_fst, ← map_smul, hAt' c hc, map_zero, Prod.fst_zero]
  have hco2 : At (evFin F v) (G.M'.co.e u').2 := by
    intro c hc
    rw [← Prod.smul_snd, ← map_smul, hAt' c hc, map_zero, Prod.snd_zero]
  have hRinv := (hRest 0 (Submodule.zero_mem _)).1
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u') (S φ) (S φ₁) := by
    apply acts_schr_of_ref v B.ψ (G.M'.co.e u') hco1 hco2 R hR0 hRinv
    have e1 := (hS φ hφ).2 R (hRest φ hφ)
    have e2 := (hS φ₁ hφ₁).2 R (hRest φ₁ hφ₁)
    have e3 := hA R (hRest φ hφ)
    have e4 := hsp.impl ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u (tens (evFin F v) φ R) (hRest φ hφ).2
    show G.M'.co.rho B.ψ u' (tens (evFin F v) (S φ) R) = tens (evFin F v) (S φ₁) R
    rw [← e1, ← e2, ← e3, hu'D]
    exact e4.symm
  exact hl u' hlag (S φ) (hS φ hφ).1 (S φ₁) (hS φ₁ hφ₁).1 hact

end GlobalTheory.InertVacEquiv
end
