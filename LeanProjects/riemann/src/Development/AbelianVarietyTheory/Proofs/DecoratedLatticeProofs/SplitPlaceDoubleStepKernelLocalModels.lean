import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummandStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSliceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTargetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourierStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRowStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastKerLoc

open GlobalTheory.LocFlat.CFac in

theorem lastLoc : ∀ (D : D7), LastLoc D := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hχ ρ B S X T L'' o'' τ hL hτ s z₀ hs hz n n' Z _ _ _ _ _ _ FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  classical
  obtain ⟨-, hck, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hck ψk hχ
  let κ : WO S L'' → WO B.L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat τ : Mx D B.L.rank L''.rank) * w)
  let Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.A S → WO S X → ℂ) :=
    LinearMap.mk₂ ℂ (fun Ψ₂ Ψ₁ u => o''.boxT S (T₂ Ψ₂) fun w => T₁ Ψ₁ ((B.o.resS S).symm (u, κ w)))
      (by intros; funext u v; simp only [OrthDec.boxT, map_add, Pi.add_apply, add_mul])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
      (by intros; funext u v; simp only [OrthDec.boxT, map_add, Pi.add_apply, mul_add])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul]; ring)
  obtain ⟨Λ, hΛ1, hΛ2⟩ := GlobalTheory.T.exists_pair_space_linear_map_via_partial_fourier k ν hν ψk hψc hψ1 n n' Z _ Bl
  obtain ⟨hXi, hPsi⟩ := GlobalTheory.T.last_column_datum_tensor_mem_schwartzBruhat k ν hν ψk hψc hψ1 n n' Z
  obtain ⟨hHat, hDec⟩ := GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row k ν hν ψk hψc hψ1 n Z
  have hBl : ∀ a Ψ u v, Bl a Ψ u v = T₂ a (o''.resT S v).1 * T₁ Ψ ((B.o.resS S).symm (u, κ (o''.resT S v).2)) :=
    fun _ _ _ _ => rfl
  refine ⟨Λ, ⟨?_, ?_⟩, ?_⟩
  · intro Ξ₂ v
    obtain ⟨N, a, c, g, hg, hsum⟩ := hDec Ξ₂
    have hsl := fun i => GlobalTheory.T.localModel_slice_firstSummand D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁ (c i) (κ (o''.resT S v).2)
    choose T' hT' hT'eq using hsl
    obtain ⟨hz0, hlin⟩ := GlobalTheory.T.splitLocalPlace_local_models_linear_subspace D k p ψ n n' B.A S FA FS
    refine ⟨∑ i, (T₂ (a i) (o''.resT S v).1) • T' i, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun T => p.IsModel ψ FA FS T) (fun _ _ h1 h2 => (hlin _ _ h1 h2).1) hz0 ?_
      intro i _
      exact (hlin _ _ (hT' i) (hT' i)).2 _
    · intro Ξ₁ Ξ hΞ u
      have hΞs : Ξ = ∑ i, prodSB Ξ₁ (g i) := by
        apply Subtype.ext
        funext q
        rw [hΞ, Submodule.coe_sum, Finset.sum_apply, hsum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
        rfl
      have hPi : ∀ i, ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * (c i).1 (Matrix.of fun r _ => x r (Sum.inr ())) :=
        fun i => hPsi Ξ₁ (c i)
      choose Ψ hΨ using hPi
      have hterm : ∀ i, Λ (prodSB Ξ₁ (g i)) = Bl (a i) (Ψ i) := fun i =>
        hΛ2 Ξ₁ (a i) (c i) (Ψ i) (prodSB Ξ₁ (g i)) (hΨ i) (fun q => by rw [prodSB_apply, hg])
      rw [hΞs, map_sum, Finset.sum_apply, Finset.sum_apply, LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm, hBl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hT'eq i Ξ₁ (Ψ i) (hΨ i) u]
  · intro Ξ₁ u
    obtain ⟨FL, hFL, hsl⟩ := GlobalTheory.T.local_model_restricted_to_line_slice D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁
    obtain ⟨TLS, hTLS, hTLSeq⟩ := hsl Ξ₁ u
    obtain ⟨FL'', hFL'', TL, hTL, hTLeq⟩ := GlobalTheory.T.lineModel_kappa_transform_isLocalModel D k p ν hν ψ hψ ψk hχ B.L S L'' B.ζ τ hL hτ s z₀ hs hz n FS FL hFL TLS hTLS
    let P : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) :=
      { toFun := fun g => prodSB Ξ₁ g
        map_add' := fun g g' => by apply Subtype.ext; funext q; simp [prodFn, mul_add]
        map_smul' := fun c g => by apply Subtype.ext; funext q; simp [prodFn]; ring }
    let TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ) := LinearMap.proj u ∘ₗ Λ ∘ₗ P
    have hTXa : ∀ g, TX g = Λ (prodSB Ξ₁ g) u := fun _ => rfl
    refine ⟨TX, GlobalTheory.T.local_model_box_product_orthogonal_sum_target D k p ψ S X T L'' o'' n Z FS FT FL'' FX ?_ T₂ TL hT₂ hTL TX ?_, ?_⟩
    · rw [hFX]
      congr 1
      ext r j
      simp [Matrix.mul_apply, hFL'', Matrix.mulVec, dotProduct]
    · intro a b Φ hΦ
      obtain ⟨c, hc⟩ := hHat b
      obtain ⟨Ψ₁, hΨ₁⟩ := hPsi Ξ₁ c
      have h := hΛ2 Ξ₁ a c Ψ₁ (prodSB Ξ₁ Φ) hΨ₁ (fun q => by rw [prodSB_apply, hΦ, hc]; rfl)
      funext v
      rw [hTXa, h, hBl, OrthDec.boxT, hTLeq c b hc, hTLSeq c Ψ₁ hΨ₁]
    · intro Ξ₂ Ξ hΞ v
      have : Ξ = prodSB Ξ₁ Ξ₂ := Subtype.ext (funext hΞ)
      subst this
      rfl
  · intro Ψ₁ Ψ₂
    obtain ⟨Ξ, hΞ⟩ := hXi Ψ₁ Ψ₂
    refine ⟨Ξ, hΞ, fun u => ?_⟩
    rw [hΛ1 Ψ₁ Ψ₂ Ξ hΞ]
    rfl

end GlobalTheory.LastKerLoc

end
