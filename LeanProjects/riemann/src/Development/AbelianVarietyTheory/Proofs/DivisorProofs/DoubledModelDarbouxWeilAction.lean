import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section
namespace GlobalTheory.DblDatumBox

theorem star_addChar {R : Type} [AddCommGroup R] (ψ : AddChar R ℂ) (h : ∀ t, ‖ψ t‖ = 1) (t : R) :
    star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h t)]
  rfl

theorem schr_neg_star {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (h : ∀ t, ‖ψ t‖ = 1)
    {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ (w.1, -w.2) (fun x => star (φ x)) = fun x => star (schr ψ w φ x) := by
  funext x
  simp only [schr, star_mul', star_addChar ψ h, dotProduct_neg]
  congr 2
  ring

theorem box_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W)
    (W₂ : Spc F E (d + d)), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    (∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), boxC Φ₁ Φ₂ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
    ∀ (u : Matrix (Fin n) (Fin (d + d)) (AE F E)), ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      e (boxC (M.co.rho B.ψ (topC u) Φ₁) (M.co.rho B.ψ (botC u) Φ₂)) = co.rho B.ψ u (e (boxC Φ₁ Φ₂)) := by
  intro F E _ _ _ _ _ σ B hB n d Xs W M W₂ _ co e _ _ he
  have h1 : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      boxC Φ₁ Φ₂ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := fun Φ₁ h₁ Φ₂ h₂ =>
    GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic F _ _ _ _ h₁ (GlobalTheory.SchAConj.star_mem_schA F _ Φ₂ h₂)
  refine ⟨h1, fun u Φ₁ h₁ Φ₂ h₂ => ?_⟩
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hB.std
  rw [← he u _ (h1 Φ₁ h₁ Φ₂ h₂)]
  congr 1
  unfold boxC
  rw [GlobalTheory.BoxSpan.schr_boxFun]
  have h2 := schr_neg_star B.ψ hψ (M.co.e (botC u)) Φ₂
  unfold Darboux.rho
  rw [← h2]
  rfl

end GlobalTheory.DblDatumBox
end
