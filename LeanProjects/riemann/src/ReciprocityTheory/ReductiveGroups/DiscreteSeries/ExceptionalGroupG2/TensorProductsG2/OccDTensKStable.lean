import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefBTensSubKStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def occQOK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool) (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D)
    (S : Submodule ℂ D) (Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ) : Prop :=
  (∀ f ∈ tensSub S, ∀ g ∈ tensSub S, Q g f = star (Q f g)) ∧
    (∀ f ∈ tensSub S, f ≠ 0 → 0 < (Q f f).re) ∧
    (∀ a b, ∀ f ∈ tensSub S, ∀ g ∈ tensSub S,
      Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) ∧
    ∀ k ∈ Kset ε, ∀ f ∈ tensSub S, ∀ g ∈ tensSub S,
      ∀ f' ∈ tensSub S, ∀ g' ∈ tensSub S,
        (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
        (fun c => ((g' c : D) : H)) = kDiag dual σ k (fun c => ((g c : D) : H)) → Q f' g' = Q f g

theorem occD_genSub_K {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x : D} (hx : x ∈ genSub E V) :
    ∃ y ∈ genSub E V, (y : H) = σ k (x : H) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hD.glRep hVk hx
  have hf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hs := KTypeIsomorphism.orbit_hasSum hσ hD hf (layer_kStable hD.glRep hVk m) hZ ⟨x, hm⟩
  let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ (layer ε E V m).subtype)
  have hmem : σ (NormedSpace.exp Z) (x : H) ∈ P :=
    P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
      P.sum_mem fun j _ => P.smul_mem _ ⟨_, rfl⟩)
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, layer_le_genSub m w.2, hw⟩

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occD_eeF (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') (s : Fin n)
    (hlam' : lam' = shiftF dual lam s) {ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε))}
    (hι : IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι) :
    ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x := by
  intro x hx
  have hE := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  have h1 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam' : ℝ) : ℂ) • ι x := by
    rw [← map_smul, ← casimir_genSub hE (datumV_casimir hP' v₀') x hx]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hι.2.2.1 a b _ (tset_genSub_E _ _ b a hx), hι.2.2.1 b a x hx]
  have h2 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x +
      (2 : ℂ) • eeF dual (smE ε (rreg ε)) (ι x) := by
    have h3 : diagOp (casimir (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x := funext fun c => by
      rw [diagOp_coord, casimir_genSub hE (datumV_casimir hP v₀) _ (tset_mem.mp (hι.1 x hx) c)]; rfl
    rw [← h3]
    cases dual
    · exact LinearMap.congr_fun (casimir_tensV hE) _
    · exact LinearMap.congr_fun (casimir_tensVd hE) _
  rw [h1, hlam', ← casVal_shiftF] at h2
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  show (2 : ℂ) • _ = (2 : ℂ) • _
  rw [smul_smul, ← add_right_inj (((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x), ← h2, ← add_smul, ← add_smul]
  push_cast; rfl

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
