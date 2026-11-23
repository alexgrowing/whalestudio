import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameTheta

theorem isOpen_frames {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) : IsOpen (FD.GG Ψ G p) := by
  have hmat : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.mat x τ := fun τ =>
    show Continuous fun x : FD.Frame Ψ r => (x τ : Matrix (Fin r) (Fin r) ℂ) from continuous_apply τ
  have hgram : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.gram τ.1 G (FD.mat x τ) := by
    intro τ
    refine continuous_matrix fun a b => ?_
    simp only [FD.gram, FD.hermC, FD.col, FD.mat, Matrix.of_apply]
    fun_prop
  have hdmin : ∀ (τ : Ψ) (i : Fin (r + 1)), Continuous fun x : FD.Frame Ψ r => FD.dmin G x τ i := by
    intro τ i
    unfold FD.dmin FD.lminor
    exact ((hgram τ).matrix_submatrix _ _).matrix_det
  unfold FD.GG
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))

theorem exists_thetaFrame_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPreconnected (FD.GG Ψ Gm (U.Di i).q) → ∀ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La), (∀ a b, (U.Di i).EF (bas a) (bas b) = -omegaStd a b) → ∀ (m : ℕ) (ι : (Fin m → ℂ) ≃L[ℂ] FD.Frame Ψ r), ∃ (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), (∀ b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q, IsUnit (h b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧ ∀ k, h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1) ∧ (∀ j k, DifferentiableOn ℂ (fun b => h b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) ∧ DifferentiableOn ℂ (fun b => τ b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q)) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => U.u i (Pf (ι b))) (fun b z => (U.ex i (Pf (ι b)) z).left) (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf hconn bas hbas m ι
  have hper := (GlobalTheory.FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ hr).2
  have hdiff := (GlobalTheory.per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ).1 Pf hPf
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas
  have hhol : IsHolPeriods (U.Di i) ty (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => Pf (ι b)) :=
    ⟨fun b hb => (hper _ hb).2 _ (hPf _), fun v =>
      (hdiff v).comp ι.differentiable.differentiableOn fun _ hb => hb⟩
  have hopen : IsOpen (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) := (isOpen_frames Ψ Gm _).preimage ι.continuous
  have hpre : IsPreconnected (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) :=
    ι.toHomeomorph.isPreconnected_preimage.2 hconn
  have hex : ∀ b : Fin m → ℂ, ∃ h τ : Matrix (Fin g) (Fin g) ℂ, b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q →
      IsUnit h.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ k,
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1 := by
    intro b
    by_cases hb : b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q
    · obtain ⟨h, τ, h1, h2, h3, h4, -⟩ := hR1 _ (hhol.1 b hb)
      exact ⟨h, τ, fun _ => ⟨h2, h3, h4, h1⟩⟩
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose h τ hhτ using hex
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := U.theta i m _ (fun b => Pf (ι b)) bas (-1) h τ hopen hpre hhol
    (fun a b => by rw [hbas]; simp) (fun b hb => ⟨(hhτ b hb).2.2.1, (hhτ b hb).2.2.2⟩)
  exact ⟨h, τ, c₁, c₂, hhτ, hR2 m _ _ h τ hhol fun b hb => (hhτ b hb).2.2.2, hc₁, hc₂, hθ⟩

end GlobalTheory.FrameTheta
