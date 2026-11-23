import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitFrameReal

theorem gram_eq {D : D7} (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X) (ρ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    gram (tauE D ρ) X.Gm z = -(zᴴ * gramAt D V ρ * z)ᵀ := by
  have hG : X.Gm.map (tauE D ρ) = -(gramAt D V ρ)ᵀ := by
    rw [hW.1]
    ext a b
    simp [gramAt]
  have hg : gram (tauE D ρ) X.Gm z = zᵀ * X.Gm.map (tauE D ρ) * zᴴᵀ := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, conjTranspose_apply, map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [hg, hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem gram_iff {D : D7} (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X) (ρ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (gram (tauE D ρ) X.Gm z = diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ↔
      zᴴ * gramAt D V ρ * z = diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1 := by
  have e : (diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) =
      -(diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1)ᵀ := by
    rw [diagonal_transpose, diagonal_neg]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [gram_eq V X hW, e, neg_inj, Matrix.transpose_inj]

theorem negFirst_unit {D : D7} {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det (h ρ)
  rw [det_mul, h0, mul_zero, det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem unit_frames : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ u y, FrIs θ V hr X x u y → IsUnitFr X y) ∧ (∀ y, IsUnitFr X y → ∃ u ∈ GinfC V, FrIs θ V hr X x u y) ∧ (∀ u, ∃ y, FrIs θ V hr X x u y) ∧ (∀ u y y', FrIs θ V hr X x u y → FrIs θ V hr X x u y' → y = y') ∧ ∀ u ∈ GinfC V, ∀ u' ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → FrIs θ V hr X x u' y → u = u' := by
  intro D θ V r hr X x hθ hM hx
  subst hr
  obtain ⟨hΨ, hW⟩ := hM
  have hre : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) A = A := fun _ => rfl
  have hmem : ∀ ρ, tauE D ρ ∈ X.Ψ := fun ρ => (hΨ _).2 ⟨ρ, rfl⟩
  choose s hs using fun τ : X.Ψ => (hΨ τ.1).1 τ.2
  have hU : ∀ u ρ, (archM V (θ ρ) u)ᴴ * gramAt D V ρ * archM V (θ ρ) u = gramAt D V ρ := fun u ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u ρ
  have hxu := negFirst_unit hx
  refine ⟨fun u y h τ => ?_, fun y hy => ?_, fun u => ?_, fun u y y' h h' => ?_, fun u hu u' hu' y h h' => ?_⟩
  · rw [h (s τ) τ (hs τ), hre, hs τ, gram_iff V X hW, ← hx (s τ), conjTranspose_mul]
    conv_rhs => rw [← hU u (s τ)]
    simp only [Matrix.mul_assoc]
  · obtain ⟨u, hu, e⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2
      (fun ρ => mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹) (fun ρ => by
        have h1 := (gram_iff V X hW ρ _).1 (hy ⟨tauE D ρ, hmem ρ⟩)
        rw [← hx ρ] at h1
        show (mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹)ᴴ * gramAt D V ρ * (mat y ⟨tauE D ρ, hmem ρ⟩ * (x ρ)⁻¹) =
          gramAt D V ρ
        calc _ = ((x ρ)⁻¹)ᴴ * ((mat y ⟨tauE D ρ, hmem ρ⟩)ᴴ * gramAt D V ρ * mat y ⟨tauE D ρ, hmem ρ⟩) * (x ρ)⁻¹ := by
              simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = (x ρ * (x ρ)⁻¹)ᴴ * gramAt D V ρ * (x ρ * (x ρ)⁻¹) := by
              rw [h1]; simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = _ := by rw [Matrix.mul_nonsing_inv _ (hxu ρ)]; simp)
    refine ⟨u, hu, fun ρ τ hτ => ?_⟩
    obtain rfl : τ = ⟨tauE D ρ, hmem ρ⟩ := Subtype.ext hτ
    rw [hre, archM_eq, e ρ, Matrix.nonsing_inv_mul_cancel_right _ _ (hxu ρ)]
  · refine ⟨fun τ => (archM V (θ (s τ)) u * x (s τ) : Matrix _ _ ℂ), fun ρ τ hτ => ?_⟩
    obtain rfl : s τ = ρ := GlobalTheory.SmoothForms.RealPts.tauE_injective D ((hs τ).symm.trans hτ)
    rfl
  · funext τ
    exact (h (s τ) τ (hs τ)).trans (h' (s τ) τ (hs τ)).symm
  · refine ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.1 u hu u' hu' fun ρ => ?_
    have h1 : archM V (θ ρ) u * x ρ = archM V (θ ρ) u' * x ρ :=
      (h ρ ⟨tauE D ρ, hmem ρ⟩ rfl).symm.trans (h' ρ ⟨tauE D ρ, hmem ρ⟩ rfl)
    have h2 := congrArg (· * (x ρ)⁻¹) h1
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ (hxu ρ)] at h2
    exact h2

end GlobalTheory.UnitFrameReal

end
