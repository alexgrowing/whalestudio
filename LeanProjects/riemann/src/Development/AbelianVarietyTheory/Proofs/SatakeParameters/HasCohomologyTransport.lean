import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

noncomputable section

namespace GlobalTheory.ConjCoh

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.ContraPair Topology
open scoped TensorProduct

variable {E : Type} [Field E] {a : ℕ}

section Transport

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  {κ : Kinf E a → Module.End ℂ M} {L : Lie E a →ₗ[ℝ] Module.End ℂ M}
  {κ' : Kinf E a → Module.End ℂ M'} {L' : Lie E a →ₗ[ℝ] Module.End ℂ M'}

def tr (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) :
    Herm E a [⋀^Fin q]→ₗ[ℝ] M' :=
  (T.restrictScalars ℝ).compAlternatingMap (ω.compLinearMap σ)

theorem tr_apply (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (X : Fin q → Herm E a) : tr σ T ω X = T (ω fun i => σ (X i)) := rfl

theorem isCochain_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} {T : M →ₗ[ℂ] M'}
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ' (tr σ T ω) := fun k X => by
  rw [tr_apply, tr_apply, ← hκ, ← hω]
  simp only [had]

theorem dCo_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {T : M →ₗ[ℂ] M'}
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m))
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : dCo L' (tr σ T ω) = tr σ T (dCo L ω) := by
  refine AlternatingMap.ext fun X => ?_
  rw [tr_apply, dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hL, tr_apply]
  rfl

theorem tr_tr {σ : Herm E a →ₗ[ℝ] Herm E a} (hσ : ∀ X, σ (σ X) = X) (T : M ≃ₗ[ℂ] M')
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : tr σ T.symm.toLinearMap (tr σ T.toLinearMap ω) = ω := by
  refine AlternatingMap.ext fun X => ?_
  simp [tr_apply, hσ]

theorem tr_zero (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} :
    tr σ T (0 : Herm E a [⋀^Fin q]→ₗ[ℝ] M) = 0 :=
  AlternatingMap.ext fun X => by simp [tr_apply]

theorem hasCohomology_transport {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} (T : M ≃ₗ[ℂ] M')
    (hσ : ∀ X, σ (σ X) = X) (hs : ∀ k, s (s k) = k)
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m)) (H : HasCohomology κ L) : HasCohomology κ' L' := by
  have hκ' : ∀ k m, T.symm (κ' (s k) m) = κ k (T.symm m) := fun k m => by
    rw [T.symm_apply_eq]
    have := hκ (s k) (T.symm m)
    rw [hs, T.apply_symm_apply] at this
    exact this.symm
  have hL' : ∀ X m, T.symm (L' (toL (σ X).1) m) = L (toL X.1) (T.symm m) := fun X m => by
    rw [T.symm_apply_eq]
    have := hL (σ X) (T.symm m)
    rw [hσ, T.apply_symm_apply] at this
    exact this.symm
  rcases H with ⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩
  · refine Or.inl ⟨tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun h => h2 ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · rw [← tr_tr hσ T ω, h, tr_zero]
  · refine Or.inr ⟨q, tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun η hη h => ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · refine h2 (tr σ T.symm.toLinearMap η) (isCochain_tr (T := T.symm.toLinearMap) had hκ' hη) ?_
      rw [dCo_tr (L := L') (T := T.symm.toLinearMap) hL', h, tr_tr hσ]

end Transport

def barG : GL (Fin a) (Cinf E) →* GL (Fin a) (Cinf E) := GeneralLinearGroup.map (starRingEnd (Cinf E))

theorem barG_val (y : GL (Fin a) (Cinf E)) (i j : Fin a) : (barG y).val i j = star (y.val i j) := rfl

theorem barG_barG (y : GL (Fin a) (Cinf E)) : barG (barG y) = y := by
  ext i j : 2
  simp [barG_val]

theorem barG_det (y : GL (Fin a) (Cinf E)) : (barG y).val.det = star y.val.det :=
  ((starRingEnd (Cinf E)).map_det y.val).symm

def barH : Herm E a →ₗ[ℝ] Herm E a where
  toFun X := ⟨X.1.map star, by
    have h : star X.1 = X.1 := X.2
    change star (X.1.map star) = X.1.map star
    ext i j : 1
    have := congrFun (congrFun h j) i
    change star (star (X.1 j i)) = star (X.1 i j)
    rw [star_star]
    exact this.symm⟩
  map_add' X Y := Subtype.ext (by ext i j; simp)
  map_smul' c X := Subtype.ext (by ext i j; simp)

variable [NumberField E] [IsTotallyComplex E]

theorem coord_star (τ : E →+* ℂ) (x : Cinf E) : coord τ (star x) = coord (ComplexEmbedding.conjugate τ) x := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    simp
  · rw [if_neg (by rw [h]; exact hne), if_pos h]
    simp

theorem regFun_comp {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) : (fun y => f (barG y)) ∈ regFun E a := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨_, i, j, funext fun y => coord_star τ _⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨ComplexEmbedding.conjugate τ, funext fun y => by
        simp only [barG_det, coord_star]⟩)
  | algebraMap c => exact Subalgebra.algebraMap_mem _ c
  | add f g _ _ h1 h2 => exact add_mem h1 h2
  | mul f g _ _ h1 h2 => exact mul_mem h1 h2

abbrev barRep (Ξ : AlgRep E a) : AlgRep E a where
  d := Ξ.d
  mat := Ξ.mat.comp barG
  reg i j := regFun_comp (Ξ.reg i j)
  pos := Ξ.pos
  irred W hW := Ξ.irred W fun y v hv => by
    have := hW (barG y) v hv
    rwa [MonoidHom.comp_apply, barG_barG] at this

def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun X Y => by ext i j; simp
      map_smul' := fun c X => by ext i j; simp }

end GlobalTheory.ConjCoh

end

namespace GlobalTheory.ConjCoh

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

end GlobalTheory.ConjCoh
