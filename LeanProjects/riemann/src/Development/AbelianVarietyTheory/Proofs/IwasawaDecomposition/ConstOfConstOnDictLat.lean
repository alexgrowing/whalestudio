import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryRealEquivariantOntoTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem const_of_const_on_dictLat : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → IsUnf U → (∀ k, ModelW V hr (U.X k)) → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictLat U V hr dict io e F ik φ th x₀ → ∀ f ∈ sec Xo c 0 0, ∀ c0 : ℂ, (∀ h, rdU U f (dict h).1 (dict h).2 = c0) → ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c f y) = c0 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hι hpq hA hσ hx hU hW hth hD f hf c0 hc y
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
    intro h
    obtain ⟨γ, -, -, -, hfr⟩ := hD.2 h
    refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X _).p0
      (U.X _).Ψ (U.X _).Gm (U.X _).Gm_herm).2.1 _ fun τ => ?_).1
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1), ← hx₀ _ τ.1 τ.2, hG]
    have hu := (hAr τ.1).2.2.2.2 (γ * h)
    have hg : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
        gram τ.1 (-V.gramᵀ) x = xᵀ * (-V.gramᵀ).map τ.1 * x.map (starRingEnd ℂ) := fun x => by
      ext a b
      simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.sum_mul]
      exact Finset.sum_comm
    change gram τ.1 _ (archM V (θ τ.1) (γ * h) * x₀ τ.1) = _
    rw [hg, hg, Matrix.transpose_mul, Matrix.map_mul]
    conv_rhs => rw [← hu]
    simp only [Matrix.mul_assoc]
  obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx₀ hdom y
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh, ← hc h]
  exact (dif_pos (hdom h) : rdU U f (dict h).1 (dict h).2 = _).symm

end GlobalTheory.Member
