import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatiosStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDominatingSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRightStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.FlagBun in
theorem GlobalTheory.CompanionTheory.Ar.exists_flagBundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L hx hirr hL
  classical
  have hc : ∀ s, ∃ c : Fin (r s) → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = V s := by
    intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := hL s ⟨genPt ξ, specializes_refl _⟩ trivial
    exact ⟨b, (hfr ⟨genPt ξ, specializes_refl _⟩ trivial hU).1, hb⟩
  choose c hc using hc
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x (L s) m φ :=
    fun s => GlobalTheory.T.exists_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) hx hirr (hL s)
  choose m n φ hφ using hg
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt ξ, specializes_refl _⟩
  have hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1 :=
    fun s => GlobalTheory.T.frame_via_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) (m s) (n s) (φ s) (c s) hx (hL s) (hφ s) (hc s).1 (hc s).2
  obtain ⟨J₀, hJ₀, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω E S r n κ x φ c c₀ hc₀.1 (GlobalTheory.T.function_field_ratio_generators X Ω ξ κ x c₀ hx hc₀.1) hB
  haveI : Finite (FlagIx κ n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx κ n r) (flagCoord κ x φ c) J₀ hJ₀ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular X Ω ξ ℤ κ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simpa using intCast_mem (regAt ξ' p') z) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord κ x φ c (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsurj := GlobalTheory.T.proper_dominating_surjective X Ω ξ κ x X' (GenField Ω r) ξ' s' f _ hx hirr hprop hdom
  have hsm := GlobalTheory.T.flag_frames_generic_model_right X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hfl := GlobalTheory.T.flag_frames_generic_model_left X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hgen := GlobalTheory.T.generic_flag_over_generic_field Ω E S r V c hc
  have hne : Nonempty (FlagIx κ n r) := ⟨J₀⟩
  have hpos : 0 < Nat.card (FlagIx κ n r) := Nat.card_pos
  let e : Fin (Nat.card (FlagIx κ n r) - 1 + 1) ≃ FlagIx κ n r :=
    (finCongr (Nat.sub_add_cancel hpos)).trans (Finite.equivFin (FlagIx κ n r)).symm
  exact ⟨X', GenField Ω r, inferInstance, inferInstance, ξ', f, _, flagCoord κ x φ c ∘ e, genB c,
    (by convert coordTie_comp_equiv hx' e using 1 <;> first | exact Subsingleton.elim _ _ | skip), hirr', hdom, hsm, hsurj, hgen, hfl⟩
